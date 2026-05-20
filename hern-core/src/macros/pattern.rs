use crate::ast::Pattern;
use crate::syntax::{
    Syntax, SyntaxCapture, SyntaxCategory, SyntaxDelimiter, SyntaxKind, SyntaxPattern, SyntaxToken,
    category_accepts_source,
};
use std::collections::HashMap;

use super::diagnostics::{MacroRuntimeError, pattern_span};
use super::source::{sequence_syntax, syntax_nodes_source, syntax_shape_eq, syntax_token_eq};
use super::value::{MacroEnv, MacroValue};

pub(super) fn match_macro_pattern(
    pattern: &Pattern,
    value: &MacroValue,
    env: &mut MacroEnv,
) -> Result<bool, MacroRuntimeError> {
    match pattern {
        Pattern::Wildcard => Ok(true),
        Pattern::Variable(name, _) => {
            env.insert(name.clone(), value.clone());
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
        _ => Err(MacroRuntimeError::new(
            pattern_span(pattern),
            "unsupported match pattern in macro body",
        )),
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
            category_accepts_source(category, &syntax_nodes_source(nodes)).unwrap_or(false)
        }
    }
}
