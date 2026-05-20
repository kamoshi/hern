use crate::ast::Pattern;
use crate::syntax::{
    Syntax, SyntaxCapture, SyntaxCategory, SyntaxDelimiter, SyntaxKind, SyntaxPattern, SyntaxToken,
    category_accepts_source,
};
use std::collections::HashMap;

use super::diagnostics::{MacroRuntimeError, pattern_span};
use super::source::{sequence_syntax, syntax_shape_eq, syntax_token_eq};
use super::value::{MacroEnv, MacroValue};

pub(super) fn match_macro_pattern(
    pattern: &Pattern,
    value: &MacroValue,
    env: &mut MacroEnv,
) -> Result<bool, MacroRuntimeError> {
    match pattern {
        Pattern::Wildcard => Ok(true),
        Pattern::StringLit(expected) => {
            Ok(matches!(value, MacroValue::String(actual) if actual == expected))
        }
        Pattern::NumberLit(crate::lex::NumberLiteral::Int(expected)) => {
            Ok(matches!(value, MacroValue::Int(actual) if actual == expected))
        }
        Pattern::NumberLit(crate::lex::NumberLiteral::Float(expected)) => {
            Ok(matches!(value, MacroValue::Float(actual) if actual == expected))
        }
        Pattern::BoolLit(expected) => {
            Ok(matches!(value, MacroValue::Bool(actual) if actual == expected))
        }
        Pattern::Variable(name, _) => {
            env.insert(name.clone(), value.clone());
            Ok(true)
        }
        Pattern::Constructor { name, binding } => {
            match_constructor_pattern(name, binding.as_deref(), value, env)
        }
        Pattern::Tuple(items) => {
            let MacroValue::Tuple(values) = value else {
                return Ok(false);
            };
            if items.len() != values.len() {
                return Ok(false);
            }
            let mut scoped = env.clone();
            for (pattern, value) in items.iter().zip(values) {
                if !match_macro_pattern(pattern, value, &mut scoped)? {
                    return Ok(false);
                }
            }
            *env = scoped;
            Ok(true)
        }
        Pattern::List { elements, rest } => {
            let values = match value {
                MacroValue::Array(values) => values,
                MacroValue::SyntaxArray(values) => {
                    if elements.len() > values.len() {
                        return Ok(false);
                    }
                    let mut scoped = env.clone();
                    for (pattern, syntax) in elements.iter().zip(values) {
                        if !match_macro_pattern(
                            pattern,
                            &MacroValue::Syntax(syntax.clone()),
                            &mut scoped,
                        )? {
                            return Ok(false);
                        }
                    }
                    match rest {
                        None if elements.len() != values.len() => return Ok(false),
                        Some(Some((name, _))) => {
                            scoped.insert(
                                name.clone(),
                                MacroValue::SyntaxArray(values[elements.len()..].to_vec()),
                            );
                        }
                        Some(None) | None => {}
                    }
                    *env = scoped;
                    return Ok(true);
                }
                _ => return Ok(false),
            };
            if elements.len() > values.len() {
                return Ok(false);
            }
            let mut scoped = env.clone();
            for (pattern, value) in elements.iter().zip(values) {
                if !match_macro_pattern(pattern, value, &mut scoped)? {
                    return Ok(false);
                }
            }
            match rest {
                None if elements.len() != values.len() => return Ok(false),
                Some(Some((name, _))) => {
                    scoped.insert(
                        name.clone(),
                        MacroValue::Array(values[elements.len()..].to_vec()),
                    );
                }
                Some(None) | None => {}
            }
            *env = scoped;
            Ok(true)
        }
        Pattern::Record { fields, rest } => {
            let MacroValue::Record(values) = value else {
                return Ok(false);
            };
            if rest.is_none() && fields.len() != values.len() {
                return Ok(false);
            }
            let mut scoped = env.clone();
            for (field, binding, _) in fields {
                let Some((_, value)) = values.iter().find(|(name, _)| name == field) else {
                    return Ok(false);
                };
                scoped.insert(binding.clone(), value.clone());
            }
            *env = scoped;
            Ok(true)
        }
        Pattern::SyntaxQuote(pattern) => {
            let MacroValue::Syntax(syntax) = value else {
                return Ok(false);
            };
            let mut captures = HashMap::new();
            if match_syntax_pattern_root(pattern, syntax, &mut captures) {
                for (name, capture) in captures {
                    env.insert(name, capture);
                }
                Ok(true)
            } else {
                Ok(false)
            }
        }
        Pattern::IntRange { .. } => Err(MacroRuntimeError::new(
            pattern_span(pattern),
            "unsupported range pattern in macro body",
        )),
    }
}

fn match_constructor_pattern(
    name: &str,
    binding: Option<&Pattern>,
    value: &MacroValue,
    env: &mut MacroEnv,
) -> Result<bool, MacroRuntimeError> {
    let payload = match (name, value) {
        ("Some", MacroValue::OptionSome(value)) => Some(value.as_ref()),
        ("None", MacroValue::OptionNone) => None,
        ("Ok", MacroValue::ResultOk(value)) => Some(value.as_ref()),
        ("Err", MacroValue::ResultErr(message)) => {
            return match binding {
                Some(pattern) => {
                    match_macro_pattern(pattern, &MacroValue::String(message.clone()), env)
                }
                None => Ok(false),
            };
        }
        ("MacroError", MacroValue::Error(message)) => {
            return match binding {
                Some(pattern) => {
                    match_macro_pattern(pattern, &MacroValue::String(message.clone()), env)
                }
                None => Ok(false),
            };
        }
        (expected, MacroValue::Variant(actual, payload)) if expected == actual => {
            payload.as_deref()
        }
        _ => return Ok(false),
    };

    match (binding, payload) {
        (Some(pattern), Some(value)) => match_macro_pattern(pattern, value, env),
        (None, None) => Ok(true),
        _ => Ok(false),
    }
}

fn match_syntax_pattern_root(
    pattern: &SyntaxPattern,
    syntax: &Syntax,
    captures: &mut HashMap<String, MacroValue>,
) -> bool {
    match (pattern, &syntax.kind) {
        (
            SyntaxPattern::Tree {
                children: pattern_children,
                ..
            },
            SyntaxKind::Tree {
                children: syntax_children,
                ..
            },
        ) => match_syntax_sequence(pattern_children, syntax_children, captures),
        _ => match_syntax_pattern(pattern, syntax, captures),
    }
}

fn match_syntax_pattern(
    pattern: &SyntaxPattern,
    syntax: &Syntax,
    captures: &mut HashMap<String, MacroValue>,
) -> bool {
    match pattern {
        SyntaxPattern::Token(expected) => {
            matches!(&syntax.kind, SyntaxKind::Token(actual) if syntax_token_eq(actual, expected))
        }
        SyntaxPattern::Tree {
            delimiter,
            children,
            ..
        } => {
            let SyntaxKind::Tree {
                delimiter: actual,
                children: actual_children,
            } = &syntax.kind
            else {
                return false;
            };
            delimiter == actual && match_syntax_sequence(children, actual_children, captures)
        }
        SyntaxPattern::Capture(capture) => {
            if !syntax_matches_category(capture.category, std::slice::from_ref(syntax)) {
                return false;
            }
            bind_capture(captures, capture, MacroValue::Syntax(syntax.clone()))
        }
    }
}

fn match_syntax_sequence(
    patterns: &[SyntaxPattern],
    nodes: &[Syntax],
    captures: &mut HashMap<String, MacroValue>,
) -> bool {
    if patterns.is_empty() {
        return nodes.is_empty();
    }
    let pattern = &patterns[0];
    if let SyntaxPattern::Capture(capture) = pattern {
        let min = if capture.repeat { 0 } else { 1 };
        for count in min..=nodes.len() {
            let (head, tail) = nodes.split_at(count);
            let mut next = captures.clone();
            let category_matches = if capture.repeat {
                head.iter().all(|node| {
                    syntax_matches_category(capture.category, std::slice::from_ref(node))
                })
            } else {
                syntax_matches_category(capture.category, head)
            };
            if category_matches {
                let value = if capture.repeat {
                    MacroValue::SyntaxArray(head.to_vec())
                } else if head.len() == 1 {
                    MacroValue::Syntax(head[0].clone())
                } else {
                    MacroValue::Syntax(sequence_syntax(head.to_vec()))
                };
                if bind_capture(&mut next, capture, value)
                    && match_syntax_sequence(&patterns[1..], tail, &mut next)
                {
                    *captures = next;
                    return true;
                }
            }
        }
        false
    } else if let Some((first, rest)) = nodes.split_first() {
        let mut next = captures.clone();
        if match_syntax_pattern(pattern, first, &mut next)
            && match_syntax_sequence(&patterns[1..], rest, &mut next)
        {
            *captures = next;
            true
        } else {
            false
        }
    } else {
        false
    }
}

fn bind_capture(
    captures: &mut HashMap<String, MacroValue>,
    capture: &SyntaxCapture,
    value: MacroValue,
) -> bool {
    if let Some(previous) = captures.get(&capture.name) {
        syntax_capture_value_eq(previous, &value)
    } else {
        captures.insert(capture.name.clone(), value);
        true
    }
}

fn syntax_capture_value_eq(lhs: &MacroValue, rhs: &MacroValue) -> bool {
    match (lhs, rhs) {
        (MacroValue::Syntax(lhs), MacroValue::Syntax(rhs)) => syntax_shape_eq(lhs, rhs),
        (MacroValue::SyntaxArray(lhs), MacroValue::SyntaxArray(rhs)) => {
            lhs.len() == rhs.len()
                && lhs
                    .iter()
                    .zip(rhs)
                    .all(|(lhs, rhs)| syntax_shape_eq(lhs, rhs))
        }
        _ => false,
    }
}

fn syntax_matches_category(category: SyntaxCategory, nodes: &[Syntax]) -> bool {
    match category {
        SyntaxCategory::Tokens => true,
        SyntaxCategory::Ident => matches!(
            nodes,
            [Syntax {
                kind: SyntaxKind::Token(SyntaxToken::Ident(_)),
                ..
            }]
        ),
        SyntaxCategory::Literal => matches!(
            nodes,
            [Syntax {
                kind: SyntaxKind::Token(SyntaxToken::Literal(_)),
                ..
            }]
        ),
        SyntaxCategory::Operator => matches!(
            nodes,
            [Syntax {
                kind: SyntaxKind::Token(SyntaxToken::Operator(_)),
                ..
            }]
        ),
        SyntaxCategory::Punct => matches!(
            nodes,
            [Syntax {
                kind: SyntaxKind::Token(SyntaxToken::Punct(_)),
                ..
            }]
        ),
        SyntaxCategory::Token => matches!(
            nodes,
            [Syntax {
                kind: SyntaxKind::Token(_),
                ..
            }]
        ),
        SyntaxCategory::Tree => matches!(
            nodes,
            [Syntax {
                kind: SyntaxKind::Tree { .. },
                ..
            }]
        ),
        SyntaxCategory::Block => matches!(
            nodes,
            [Syntax {
                kind: SyntaxKind::Tree {
                    delimiter: SyntaxDelimiter::Brace,
                    ..
                },
                ..
            }]
        ),
        SyntaxCategory::Expr | SyntaxCategory::Type | SyntaxCategory::Pat => {
            if nodes.is_empty() {
                return false;
            }
            category_accepts_source(category, &crate::syntax::syntax_nodes_to_source(nodes))
                .unwrap_or(false)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{ExprKind, SourceSpan};
    use crate::lex::Lexer;
    use crate::parse::Parser;
    use crate::syntax::{ScopeSet, SyntaxTemplate};

    fn quote_children(source: &str) -> Vec<Syntax> {
        let quoted = format!("'{{{source}}}");
        let tokens = Lexer::new(&quoted)
            .tokenize()
            .expect("quoted source should lex");
        let expr = Parser::new(&tokens)
            .parse_expr_fragment()
            .expect("quoted source should parse");
        let ExprKind::SyntaxQuote(SyntaxTemplate::Tree { children, .. }) = expr.kind else {
            panic!("quoted source should parse as a syntax quote tree");
        };
        children
            .into_iter()
            .map(template_to_source_syntax)
            .collect()
    }

    fn template_to_source_syntax(template: SyntaxTemplate) -> Syntax {
        match template {
            SyntaxTemplate::Token { token, span } => Syntax {
                kind: SyntaxKind::Token(token),
                span,
                origin: crate::syntax::SyntaxOrigin::Source(span),
                scopes: ScopeSet::source(),
            },
            SyntaxTemplate::Tree {
                delimiter,
                children,
                span,
            } => Syntax {
                kind: SyntaxKind::Tree {
                    delimiter,
                    children: children
                        .into_iter()
                        .map(template_to_source_syntax)
                        .collect(),
                },
                span,
                origin: crate::syntax::SyntaxOrigin::Source(span),
                scopes: ScopeSet::source(),
            },
            SyntaxTemplate::Splice { .. } => {
                panic!("golden category corpus should not contain template splices")
            }
        }
    }

    #[test]
    fn macro_pattern_categories_match_static_parser_golden_corpus() {
        let cases = [
            (SyntaxCategory::Expr, "x.y", true),
            (SyntaxCategory::Expr, "matrix[0][1]", true),
            (SyntaxCategory::Expr, "#{ x: 1 }", true),
            (SyntaxCategory::Expr, "+", false),
            (SyntaxCategory::Type, "[int]", true),
            (SyntaxCategory::Type, "#{ x: int }", true),
            (SyntaxCategory::Type, "x + y", false),
            (SyntaxCategory::Pat, "Some((x, y))", true),
            (SyntaxCategory::Pat, "#{ x, ..rest }", true),
            (SyntaxCategory::Pat, "[..rest]", true),
            (SyntaxCategory::Pat, "x +", false),
            (SyntaxCategory::Ident, "name", true),
            (SyntaxCategory::Ident, "name.field", false),
            (SyntaxCategory::Literal, "42", true),
            (SyntaxCategory::Literal, "name", false),
            (SyntaxCategory::Operator, "+", true),
            (SyntaxCategory::Operator, "name", false),
            (SyntaxCategory::Punct, ",", true),
            (SyntaxCategory::Punct, "+", false),
            (SyntaxCategory::Token, "name", true),
            (SyntaxCategory::Token, "()", false),
            (SyntaxCategory::Tree, "()", true),
            (SyntaxCategory::Tree, "name", false),
            (SyntaxCategory::Block, "{}", true),
            (SyntaxCategory::Block, "()", false),
            (SyntaxCategory::Tokens, "", true),
            (SyntaxCategory::Tokens, "x + y", true),
        ];

        for (category, source, expected) in cases {
            let nodes = quote_children(source);
            assert_eq!(
                syntax_matches_category(category, &nodes),
                expected,
                "macro pattern category {} disagreed for `{source}`",
                category.as_str()
            );
            if matches!(
                category,
                SyntaxCategory::Expr | SyntaxCategory::Type | SyntaxCategory::Pat
            ) {
                assert_eq!(
                    category_accepts_source(category, source).unwrap_or(false),
                    expected,
                    "static parser category {} disagreed for `{source}`",
                    category.as_str()
                );
            }
        }
    }

    #[test]
    fn empty_nodes_only_match_tokens_category() {
        let empty: [Syntax; 0] = [];
        assert!(syntax_matches_category(SyntaxCategory::Tokens, &empty));
        for category in [
            SyntaxCategory::Expr,
            SyntaxCategory::Type,
            SyntaxCategory::Pat,
            SyntaxCategory::Ident,
            SyntaxCategory::Literal,
            SyntaxCategory::Operator,
            SyntaxCategory::Punct,
            SyntaxCategory::Token,
            SyntaxCategory::Tree,
            SyntaxCategory::Block,
        ] {
            assert!(
                !syntax_matches_category(category, &empty),
                "empty node list should not match {}",
                category.as_str()
            );
        }
    }

    #[test]
    fn generated_synthetic_span_is_not_required_for_category_matching() {
        let node = Syntax {
            kind: SyntaxKind::Token(SyntaxToken::Ident("x".to_string())),
            span: SourceSpan::synthetic(),
            origin: crate::syntax::SyntaxOrigin::Generated,
            scopes: ScopeSet::generated(),
        };

        assert!(syntax_matches_category(SyntaxCategory::Ident, &[node]));
    }
}
