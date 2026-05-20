use crate::lex::error::{LexErrorKind, ParseError};
use crate::lex::{Lexer, Spanned, Token};
use crate::parse::Parser;

use super::SyntaxCategory;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CategoryMatchMode {
    StaticParser,
    RuntimeSyntax,
}

pub fn category_match_mode(category: SyntaxCategory) -> CategoryMatchMode {
    match category {
        SyntaxCategory::Expr | SyntaxCategory::Type | SyntaxCategory::Pat => {
            CategoryMatchMode::StaticParser
        }
        SyntaxCategory::Ident
        | SyntaxCategory::Literal
        | SyntaxCategory::Operator
        | SyntaxCategory::Punct
        | SyntaxCategory::Token
        | SyntaxCategory::Tree
        | SyntaxCategory::Block
        | SyntaxCategory::Tokens => CategoryMatchMode::RuntimeSyntax,
    }
}

pub fn category_accepts_source(category: SyntaxCategory, source: &str) -> Result<bool, ParseError> {
    let tokens = Lexer::new(source).tokenize().map_err(|err| {
        let message = match err.kind {
            LexErrorKind::UnexpectedChar(ch) => format!("unexpected character `{ch}`"),
            LexErrorKind::UnterminatedString => "unterminated string".to_string(),
            LexErrorKind::ReservedIdentifier => "reserved identifier".to_string(),
        };
        ParseError::new(message, err.span)
    })?;
    category_accepts_tokens(category, &tokens)
}

pub fn category_accepts_tokens(
    category: SyntaxCategory,
    tokens: &[Spanned],
) -> Result<bool, ParseError> {
    let parser = Parser::new(tokens);
    match category {
        SyntaxCategory::Expr => parser.parse_expr_fragment().map(|_| true),
        SyntaxCategory::Type => parser.parse_type_fragment().map(|_| true),
        SyntaxCategory::Pat => parser.parse_pattern_fragment().map(|_| true),
        SyntaxCategory::Ident => Ok(matches!(
            tokens,
            [
                Spanned {
                    token: Token::Ident(_),
                    ..
                },
                Spanned {
                    token: Token::Eof,
                    ..
                }
            ]
        )),
        SyntaxCategory::Literal => Ok(matches!(
            tokens,
            [
                Spanned {
                    token: Token::Number(_)
                        | Token::StringLit(_)
                        | Token::InterpolatedString(_)
                        | Token::True
                        | Token::False,
                    ..
                },
                Spanned {
                    token: Token::Eof,
                    ..
                }
            ]
        )),
        SyntaxCategory::Operator => Ok(matches!(
            tokens,
            [
                Spanned {
                    token: Token::Equal
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
                        | Token::DotDotEq
                        | Token::DotDot,
                    ..
                },
                Spanned {
                    token: Token::Eof,
                    ..
                }
            ]
        )),
        SyntaxCategory::Punct => Ok(matches!(
            tokens,
            [
                Spanned {
                    token: Token::Colon
                        | Token::ColonColon
                        | Token::Semicolon
                        | Token::Comma
                        | Token::Dot
                        | Token::Hash
                        | Token::InnerAttr(_)
                        | Token::Quote,
                    ..
                },
                Spanned {
                    token: Token::Eof,
                    ..
                }
            ]
        )),
        SyntaxCategory::Token => Ok(matches!(
            tokens,
            [
                Spanned {
                    token: token @ _,
                    ..
                },
                Spanned {
                    token: Token::Eof,
                    ..
                }
            ] if !matches!(
                token,
                Token::LParen
                    | Token::RParen
                    | Token::LBrace
                    | Token::RBrace
                    | Token::LBracket
                    | Token::RBracket
                    | Token::Eof
            )
        )),
        SyntaxCategory::Tree | SyntaxCategory::Block | SyntaxCategory::Tokens => Ok(false),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn accepts(category: SyntaxCategory, source: &str) -> bool {
        category_accepts_source(category, source).unwrap_or(false)
    }

    #[test]
    fn expression_category_uses_real_parser_for_postfix_forms() {
        assert!(accepts(SyntaxCategory::Expr, "x.y"));
        assert!(accepts(SyntaxCategory::Expr, "matrix[0][1]"));
        assert!(accepts(SyntaxCategory::Expr, "if true { 1 } else { 2 }"));
    }

    #[test]
    fn expression_category_rejects_partial_expressions() {
        assert!(!accepts(SyntaxCategory::Expr, "x."));
        assert!(!accepts(SyntaxCategory::Expr, "x +"));
    }

    #[test]
    fn type_and_pattern_categories_share_parser_fragments() {
        assert!(accepts(SyntaxCategory::Type, "[int]"));
        assert!(accepts(SyntaxCategory::Pat, "Some((x, y))"));
        assert!(!accepts(SyntaxCategory::Type, "[int"));
        assert!(!accepts(SyntaxCategory::Pat, "Some("));
    }

    #[test]
    fn category_match_mode_marks_parser_backed_categories() {
        assert_eq!(
            category_match_mode(SyntaxCategory::Expr),
            CategoryMatchMode::StaticParser
        );
        assert_eq!(
            category_match_mode(SyntaxCategory::Type),
            CategoryMatchMode::StaticParser
        );
        assert_eq!(
            category_match_mode(SyntaxCategory::Pat),
            CategoryMatchMode::StaticParser
        );
        assert_eq!(
            category_match_mode(SyntaxCategory::Ident),
            CategoryMatchMode::RuntimeSyntax
        );
        assert_eq!(
            category_match_mode(SyntaxCategory::Tokens),
            CategoryMatchMode::RuntimeSyntax
        );
    }
}
