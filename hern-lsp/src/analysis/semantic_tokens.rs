use hern_core::ast::{Program, SourceSpan};
use hern_core::lex::{Lexer, Token};
use hern_core::module::GraphInference;
use hern_core::source_index::{DefinitionKind, SourceIndex, index_program};
use hern_core::types::Ty;
use lsp_types::{
    SemanticToken, SemanticTokenModifier, SemanticTokenType, SemanticTokens, SemanticTokensLegend,
    SemanticTokensResult,
};
use std::collections::HashMap;

const TY_KEYWORD: u32 = 0;
const TY_VARIABLE: u32 = 1;
const TY_TYPE: u32 = 2;
const TY_NUMBER: u32 = 3;
const TY_STRING: u32 = 4;
const TY_OPERATOR: u32 = 5;
const TY_COMMENT: u32 = 6;
const TY_FUNCTION: u32 = 7;
const TY_METHOD: u32 = 8;
const TY_ENUM_MEMBER: u32 = 9;
const TY_PARAMETER: u32 = 10;
const TY_PROPERTY: u32 = 11;
const TY_TYPE_PARAMETER: u32 = 12;

const MOD_DECLARATION: u32 = 1 << 0;

#[derive(Debug, Clone, Eq, PartialEq)]
struct RawToken {
    line: u32,
    col: u32,
    len: u32,
    token_type: u32,
    token_mods: u32,
}

pub(crate) fn legend() -> SemanticTokensLegend {
    let token_types = vec![
        SemanticTokenType::KEYWORD,        // TY_KEYWORD = 0
        SemanticTokenType::VARIABLE,       // TY_VARIABLE = 1
        SemanticTokenType::TYPE,           // TY_TYPE = 2
        SemanticTokenType::NUMBER,         // TY_NUMBER = 3
        SemanticTokenType::STRING,         // TY_STRING = 4
        SemanticTokenType::OPERATOR,       // TY_OPERATOR = 5
        SemanticTokenType::COMMENT,        // TY_COMMENT = 6
        SemanticTokenType::FUNCTION,       // TY_FUNCTION = 7
        SemanticTokenType::METHOD,         // TY_METHOD = 8
        SemanticTokenType::ENUM_MEMBER,    // TY_ENUM_MEMBER = 9
        SemanticTokenType::PARAMETER,      // TY_PARAMETER = 10
        SemanticTokenType::PROPERTY,       // TY_PROPERTY = 11
        SemanticTokenType::TYPE_PARAMETER, // TY_TYPE_PARAMETER = 12
    ];
    debug_assert_eq!(token_types[TY_KEYWORD as usize], SemanticTokenType::KEYWORD);
    debug_assert_eq!(
        token_types[TY_VARIABLE as usize],
        SemanticTokenType::VARIABLE
    );
    debug_assert_eq!(token_types[TY_TYPE as usize], SemanticTokenType::TYPE);
    debug_assert_eq!(token_types[TY_NUMBER as usize], SemanticTokenType::NUMBER);
    debug_assert_eq!(token_types[TY_STRING as usize], SemanticTokenType::STRING);
    debug_assert_eq!(
        token_types[TY_OPERATOR as usize],
        SemanticTokenType::OPERATOR
    );
    debug_assert_eq!(token_types[TY_COMMENT as usize], SemanticTokenType::COMMENT);
    debug_assert_eq!(
        token_types[TY_FUNCTION as usize],
        SemanticTokenType::FUNCTION
    );
    debug_assert_eq!(token_types[TY_METHOD as usize], SemanticTokenType::METHOD);
    debug_assert_eq!(
        token_types[TY_ENUM_MEMBER as usize],
        SemanticTokenType::ENUM_MEMBER
    );
    debug_assert_eq!(
        token_types[TY_PARAMETER as usize],
        SemanticTokenType::PARAMETER
    );
    debug_assert_eq!(
        token_types[TY_PROPERTY as usize],
        SemanticTokenType::PROPERTY
    );
    debug_assert_eq!(
        token_types[TY_TYPE_PARAMETER as usize],
        SemanticTokenType::TYPE_PARAMETER
    );
    SemanticTokensLegend {
        token_types,
        token_modifiers: vec![SemanticTokenModifier::DECLARATION],
    }
}

pub(crate) fn semantic_tokens_for_source(
    source: &str,
    program: Option<&Program>,
    context: Option<SemanticContext<'_>>,
) -> SemanticTokensResult {
    let mut raw = lex_tokens(source);
    if let Some(program) = program {
        apply_semantic_overrides(&mut raw, &index_program(program), source, context);
    }
    raw.sort_by_key(|token| (token.line, token.col, token.len));
    raw.dedup_by_key(|token| (token.line, token.col, token.len));
    SemanticTokensResult::Tokens(SemanticTokens {
        result_id: None,
        data: delta_encode(raw),
    })
}

pub(crate) struct SemanticContext<'a> {
    inference: &'a GraphInference,
    module_name: &'a str,
}

impl<'a> SemanticContext<'a> {
    pub(crate) fn new(inference: &'a GraphInference, module_name: &'a str) -> Option<Self> {
        Some(Self {
            inference,
            module_name,
        })
    }
}

fn lex_tokens(source: &str) -> Vec<RawToken> {
    let mut raw = Vec::new();
    let Ok(tokens) = Lexer::new(source).tokenize() else {
        scan_line_comments(source, &mut raw);
        return raw;
    };

    for token in tokens {
        let Some(token_type) = lexical_token_type(&token.token) else {
            continue;
        };
        if token.span.len == 0 {
            continue;
        }
        raw.push(RawToken {
            line: token.span.line.saturating_sub(1) as u32,
            col: token.span.col.saturating_sub(1) as u32,
            len: token.span.len as u32,
            token_type,
            token_mods: 0,
        });
    }
    scan_line_comments(source, &mut raw);
    raw
}

fn lexical_token_type(token: &Token) -> Option<u32> {
    Some(match token {
        Token::Let
        | Token::Mut
        | Token::Fn
        | Token::If
        | Token::Else
        | Token::Trait
        | Token::Impl
        | Token::For
        | Token::Type
        | Token::Match
        | Token::Loop
        | Token::Break
        | Token::Continue
        | Token::Return
        | Token::Extern
        | Token::Import
        | Token::True
        | Token::False
        | Token::In => TY_KEYWORD,
        Token::Ident(name) if name.starts_with('\'') => TY_TYPE_PARAMETER,
        Token::Ident(_) => TY_VARIABLE,
        Token::Number(_) => TY_NUMBER,
        Token::StringLit(_) => TY_STRING,
        Token::Equal
        | Token::EqEq
        | Token::Plus
        | Token::Minus
        | Token::Arrow
        | Token::Star
        | Token::AmpAmp
        | Token::PipePipe
        | Token::PipeArrow
        | Token::Bang
        | Token::BangEq
        | Token::Op(_)
        | Token::Pipe
        | Token::DotDot
        | Token::Dot => TY_OPERATOR,
        Token::Eof
        | Token::Colon
        | Token::Semicolon
        | Token::Comma
        | Token::LParen
        | Token::RParen
        | Token::LBrace
        | Token::RBrace
        | Token::LBracket
        | Token::RBracket
        | Token::Hash => return None,
    })
}

fn apply_semantic_overrides(
    raw: &mut Vec<RawToken>,
    index: &SourceIndex,
    source: &str,
    context: Option<SemanticContext<'_>>,
) {
    // Build a position index into `raw` for O(1) override lookups instead of O(n) scans.
    let mut pos_to_idx: HashMap<(u32, u32), usize> = raw
        .iter()
        .enumerate()
        .map(|(i, t)| ((t.line, t.col), i))
        .collect();

    let mut by_symbol = HashMap::new();
    for definition in &index.definitions {
        let token_type = semantic_type_for_definition(
            definition.kind,
            definition_type(context.as_ref(), definition.location.span, &definition.name),
        );
        by_symbol.insert(definition.symbol, token_type);
        push_semantic_span(
            raw,
            &mut pos_to_idx,
            source,
            definition.location.span,
            token_type,
            MOD_DECLARATION,
        );
    }
    for reference in &index.references {
        let Some(token_type) = by_symbol.get(&reference.symbol).copied() else {
            continue;
        };
        push_semantic_span(
            raw,
            &mut pos_to_idx,
            source,
            reference.location.span,
            token_type,
            0,
        );
    }
    for reference in &index.import_member_references {
        push_semantic_span(
            raw,
            &mut pos_to_idx,
            source,
            reference.location.span,
            import_member_token_type(
                context.as_ref(),
                &reference.module_name,
                &reference.member_name,
            ),
            0,
        );
    }
}

fn semantic_type_for_definition(kind: DefinitionKind, ty: Option<&Ty>) -> u32 {
    match kind {
        DefinitionKind::Function | DefinitionKind::Extern => TY_FUNCTION,
        DefinitionKind::ImplMethod | DefinitionKind::TraitMethod => TY_METHOD,
        DefinitionKind::Let if ty.is_some_and(is_function_type) => TY_FUNCTION,
        DefinitionKind::Let => TY_VARIABLE,
        DefinitionKind::Parameter => TY_PARAMETER,
        DefinitionKind::Trait | DefinitionKind::Type | DefinitionKind::TypeAlias => TY_TYPE,
        DefinitionKind::Variant => TY_ENUM_MEMBER,
    }
}

fn definition_type<'a>(
    context: Option<&'a SemanticContext<'_>>,
    span: SourceSpan,
    name: &str,
) -> Option<&'a Ty> {
    let context = context?;
    context
        .inference
        .definition_schemes_for_module(context.module_name)
        .and_then(|schemes| schemes.get(&span))
        .map(|scheme| &scheme.ty)
        .or_else(|| {
            context
                .inference
                .binding_types_for_module(context.module_name)
                .and_then(|types| types.get(&span))
        })
        .or_else(|| {
            context
                .inference
                .env_for_module(context.module_name)
                .and_then(|env| env.get(name))
                .map(|info| &info.scheme.ty)
        })
}

fn import_member_token_type(
    context: Option<&SemanticContext<'_>>,
    module_name: &str,
    member_name: &str,
) -> u32 {
    let Some(context) = context else {
        return TY_PROPERTY;
    };
    let Some(Ty::Record(row)) = context.inference.import_types.get(module_name) else {
        return TY_PROPERTY;
    };
    row.fields
        .iter()
        .find(|(name, _)| name == member_name)
        .map(|(_, ty)| {
            if is_function_type(ty) {
                TY_METHOD
            } else {
                TY_PROPERTY
            }
        })
        .unwrap_or(TY_PROPERTY)
}

fn is_function_type(ty: &Ty) -> bool {
    match ty {
        Ty::Func(_, _) => true,
        Ty::Qualified(_, inner) => is_function_type(inner),
        _ => false,
    }
}

fn push_semantic_span(
    raw: &mut Vec<RawToken>,
    pos_to_idx: &mut HashMap<(u32, u32), usize>,
    source: &str,
    span: SourceSpan,
    token_type: u32,
    token_mods: u32,
) {
    let Some((line, col, len)) = span_to_token_position(source, span) else {
        return;
    };
    if let Some(&idx) = pos_to_idx.get(&(line, col)) {
        raw[idx].token_type = token_type;
        raw[idx].token_mods = token_mods;
        raw[idx].len = len;
    } else {
        let idx = raw.len();
        pos_to_idx.insert((line, col), idx);
        raw.push(RawToken {
            line,
            col,
            len,
            token_type,
            token_mods,
        });
    }
}

fn span_to_token_position(source: &str, span: SourceSpan) -> Option<(u32, u32, u32)> {
    let line = source.lines().nth(span.start_line.checked_sub(1)?)?;
    let start_byte = span.start_col.checked_sub(1)?;
    let end_byte = span.end_col.checked_sub(1)?.min(line.len());
    if start_byte >= end_byte || start_byte > line.len() {
        return None;
    }
    let start = byte_to_utf16_col(line, start_byte);
    let end = byte_to_utf16_col(line, end_byte);
    Some((span.start_line.saturating_sub(1) as u32, start, end - start))
}

fn byte_to_utf16_col(line: &str, byte: usize) -> u32 {
    line[..byte.min(line.len())]
        .chars()
        .map(|ch| ch.len_utf16() as u32)
        .sum()
}

fn delta_encode(raw: Vec<RawToken>) -> Vec<SemanticToken> {
    let mut out = Vec::with_capacity(raw.len());
    let mut prev_line = 0;
    let mut prev_col = 0;
    for token in raw {
        let delta_line = token.line - prev_line;
        let delta_start = if delta_line == 0 {
            token.col - prev_col
        } else {
            token.col
        };
        out.push(SemanticToken {
            delta_line,
            delta_start,
            length: token.len,
            token_type: token.token_type,
            token_modifiers_bitset: token.token_mods,
        });
        prev_line = token.line;
        prev_col = token.col;
    }
    out
}

fn scan_line_comments(source: &str, out: &mut Vec<RawToken>) {
    for (line_idx, line) in source.lines().enumerate() {
        let Some(start) = find_line_comment_start(line) else {
            continue;
        };
        out.push(RawToken {
            line: line_idx as u32,
            col: byte_to_utf16_col(line, start),
            len: line[start..].chars().map(|ch| ch.len_utf16() as u32).sum(),
            token_type: TY_COMMENT,
            token_mods: 0,
        });
    }
}

fn find_line_comment_start(line: &str) -> Option<usize> {
    let bytes = line.as_bytes();
    let mut idx = 0;
    let mut in_string = false;
    while idx + 1 < bytes.len() {
        match bytes[idx] {
            b'"' => {
                in_string = !in_string;
                idx += 1;
            }
            b'\\' if in_string => idx += 2,
            b'/' if !in_string && bytes[idx + 1] == b'/' => return Some(idx),
            _ => idx += 1,
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;
    use hern_core::pipeline::{infer_program, parse_source};
    use hern_core::types::Row;

    fn token_tuples(result: SemanticTokensResult) -> Vec<(u32, u32, u32, u32, u32)> {
        let SemanticTokensResult::Tokens(tokens) = result else {
            panic!("expected full semantic tokens");
        };
        let mut line = 0;
        let mut col = 0;
        tokens
            .data
            .into_iter()
            .map(|token| {
                line += token.delta_line;
                col = if token.delta_line == 0 {
                    col + token.delta_start
                } else {
                    token.delta_start
                };
                (
                    line,
                    col,
                    token.length,
                    token.token_type,
                    token.token_modifiers_bitset,
                )
            })
            .collect()
    }

    #[test]
    fn lexer_tokens_include_keywords_numbers_strings_and_comments() {
        let tokens = token_tuples(semantic_tokens_for_source(
            "let value = 1; // comment\n\"hi\"\n",
            None,
            None,
        ));

        assert!(tokens.iter().any(|token| token.3 == TY_KEYWORD));
        assert!(tokens.iter().any(|token| token.3 == TY_NUMBER));
        assert!(tokens.iter().any(|token| token.3 == TY_STRING));
        assert!(tokens.iter().any(|token| token.3 == TY_COMMENT));
    }

    #[test]
    fn semantic_overrides_classify_definitions_and_references() {
        let program = parse_source("fn value(x) { x }\nvalue(1)\n").expect("source should parse");
        let tokens = token_tuples(semantic_tokens_for_source(
            "fn value(x) { x }\nvalue(1)\n",
            Some(&program),
            None,
        ));

        assert!(tokens.iter().any(|token| {
            token.0 == 0 && token.1 == 3 && token.3 == TY_FUNCTION && token.4 == MOD_DECLARATION
        }));
        assert!(tokens.iter().any(|token| {
            token.0 == 0 && token.1 == 9 && token.3 == TY_PARAMETER && token.4 == MOD_DECLARATION
        }));
        assert!(tokens.iter().any(|token| {
            token.0 == 1 && token.1 == 0 && token.3 == TY_FUNCTION && token.4 == 0
        }));
    }

    #[test]
    fn semantic_tokens_classify_let_bound_functions_from_inference() {
        let source = "let id = fn(x) { x };\nid(1)\n";
        let mut program = parse_source(source).expect("source should parse");
        let inference = infer_program(&mut program).expect("source should infer");
        let graph_inference = graph_inference_for_test("main", inference);

        let tokens = token_tuples(semantic_tokens_for_source(
            source,
            Some(&program),
            SemanticContext::new(&graph_inference, "main"),
        ));

        assert!(tokens.iter().any(|token| {
            token.0 == 0 && token.1 == 4 && token.3 == TY_FUNCTION && token.4 == MOD_DECLARATION
        }));
        assert!(
            tokens
                .iter()
                .any(|token| { token.0 == 1 && token.1 == 0 && token.3 == TY_FUNCTION })
        );
    }

    #[test]
    fn semantic_tokens_classify_imported_function_members_as_methods() {
        let source = "let dep = import \"dep\";\ndep.add(1)\n";
        let program = parse_source(source).expect("source should parse");
        let mut graph_inference = GraphInference::default();
        graph_inference.import_types.insert(
            "dep".to_string(),
            Ty::Record(Row {
                fields: vec![(
                    "add".to_string(),
                    Ty::Func(
                        hern_core::types::value_func_params(vec![Ty::F64]),
                        hern_core::types::value_func_return(Ty::F64),
                    ),
                )],
                tail: Box::new(Ty::Unit),
            }),
        );

        let tokens = token_tuples(semantic_tokens_for_source(
            source,
            Some(&program),
            SemanticContext::new(&graph_inference, "main"),
        ));

        assert!(
            tokens
                .iter()
                .any(|token| { token.0 == 1 && token.1 == 4 && token.3 == TY_METHOD })
        );
    }

    fn graph_inference_for_test(
        module: &str,
        inference: hern_core::types::infer::InferenceResult,
    ) -> GraphInference {
        GraphInference {
            envs: HashMap::from([(module.to_string(), inference.env)]),
            variant_envs: HashMap::from([(module.to_string(), inference.variant_env)]),
            expr_types: HashMap::from([(module.to_string(), inference.expr_types)]),
            symbol_types: HashMap::from([(module.to_string(), inference.symbol_types)]),
            binding_types: HashMap::from([(module.to_string(), inference.binding_types)]),
            definition_schemes: HashMap::from([(module.to_string(), inference.definition_schemes)]),
            ..GraphInference::default()
        }
    }
}
