use crate::analysis::CompilerDiagnostic;
use crate::ast::{Program, SourceSpan, Stmt};
use crate::lex::error::{LexError, LexErrorKind, ParseError};
use crate::lex::{Lexer, Spanned};
use crate::parse::Parser;
use crate::reassoc::{ReassocError, build_fixity_table, reassoc_program};
use crate::types::infer::{Infer, InferenceResult, ModuleInference, TypeEnv};

/// Tokenizes `source` into a token stream.
///
/// Fail-fast: returns the first lex error and stops. Lex recovery is not currently supported;
/// there is no way to continue past a lex error.
pub fn lex_source(source: &str) -> Result<Vec<Spanned>, CompilerDiagnostic> {
    Lexer::new(source).tokenize().map_err(lex_diagnostic)
}

/// Parses a pre-lexed token stream into an AST.
///
/// Fail-fast: returns the first parse error and stops. Use [`parse_tokens_recovering`] if you
/// need a partial AST with collected diagnostics.
pub fn parse_tokens(tokens: &[Spanned]) -> Result<Program, CompilerDiagnostic> {
    Parser::new(tokens)
        .parse_program()
        .map_err(parse_diagnostic)
}

/// Lexes and parses `source` into an AST.
///
/// Fail-fast on both lex and parse: returns the first error. Use [`parse_source_recovering`]
/// for partial results, or [`lex_source`] + [`parse_tokens_recovering`] to recover only at the
/// parse level.
pub fn parse_source(source: &str) -> Result<Program, CompilerDiagnostic> {
    let tokens = lex_source(source)?;
    parse_tokens(&tokens)
}

#[derive(Debug, Clone)]
pub struct ParsedProgram {
    pub program: Program,
    pub diagnostics: Vec<CompilerDiagnostic>,
}

#[derive(Debug, Clone)]
pub struct AnalysisOutput<T> {
    pub value: Option<T>,
    pub diagnostics: Vec<CompilerDiagnostic>,
}

impl<T> AnalysisOutput<T> {
    pub fn success(value: T) -> Self {
        Self {
            value: Some(value),
            diagnostics: Vec::new(),
        }
    }

    pub fn partial(value: T, diagnostics: Vec<CompilerDiagnostic>) -> Self {
        Self {
            value: Some(value),
            diagnostics,
        }
    }

    pub fn diagnostics(diagnostics: Vec<CompilerDiagnostic>) -> Self {
        Self {
            value: None,
            diagnostics,
        }
    }

    pub fn into_result(self) -> Result<T, Vec<CompilerDiagnostic>> {
        match (self.value, self.diagnostics.is_empty()) {
            (Some(value), true) => Ok(value),
            (_, _) => Err(self.diagnostics),
        }
    }
}

/// Parses a pre-lexed token stream with parser-level statement recovery.
///
/// Failed top-level statements are skipped and collected as diagnostics; a partial AST is
/// always returned. Lex errors are not applicable since tokens are already provided.
pub fn parse_tokens_recovering(tokens: &[Spanned]) -> ParsedProgram {
    let (program, diagnostics) = Parser::new_recovering(tokens).parse_program_recovering();
    ParsedProgram {
        program,
        diagnostics: diagnostics.into_iter().map(parse_diagnostic).collect(),
    }
}

/// Parses source with parser-level statement recovery.
///
/// Lexing is still fail-fast: if tokenization fails, no partial token stream is available and this
/// returns the first lex diagnostic.
pub fn parse_source_recovering(source: &str) -> Result<ParsedProgram, CompilerDiagnostic> {
    let tokens = lex_source(source)?;
    Ok(parse_tokens_recovering(&tokens))
}

pub fn reassociate_with_program(
    program: &mut Program,
    fixity_source: &Program,
) -> Result<(), CompilerDiagnostic> {
    let mut fixity = build_fixity_table(fixity_source);
    fixity.extend(build_fixity_table(program));
    reassoc_program(program, &fixity).map_err(reassoc_diagnostic)
}

pub fn reassociate_standalone(program: &mut Program) -> Result<(), CompilerDiagnostic> {
    let fixity = build_fixity_table(program);
    reassoc_program(program, &fixity).map_err(reassoc_diagnostic)
}

/// Runs type inference on `program`.
///
/// Fail-fast: returns the first type error. Use [`infer_graph_collecting`] for whole-workspace
/// inference that collects all module diagnostics.
pub fn infer_program(program: &mut Program) -> Result<InferenceResult, CompilerDiagnostic> {
    infer_program_with_seed(program, &[], None)
}

/// Runs type inference on `program` seeded with declarations from another scope.
///
/// Fail-fast: returns the first type error encountered. Seed statements are injected before the
/// program so callers can provide prelude bindings or other ambient declarations.
pub fn infer_program_with_seed(
    program: &mut Program,
    seed_stmts: &[Stmt],
    seed_env: Option<&TypeEnv>,
) -> Result<InferenceResult, CompilerDiagnostic> {
    let mut infer = Infer::new();
    infer
        .infer_program_with_seed_and_types(program, seed_stmts, seed_env)
        .map_err(|err| CompilerDiagnostic::error(err.span, err.to_string()))
}

/// Runs type inference on `program`, collecting independent top-level diagnostics.
///
/// Unlike [`infer_program`], this returns partial inference state for declarations that remained
/// well-typed after recovery. Dependent top-level declarations are skipped rather than diagnosed
/// again to avoid cascaded errors.
pub fn infer_program_collecting(program: &mut Program) -> AnalysisOutput<ModuleInference> {
    infer_program_collecting_with_seed(program, &[], None)
}

/// Runs collecting type inference on `program` seeded with declarations from another scope.
pub fn infer_program_collecting_with_seed(
    program: &mut Program,
    seed_stmts: &[Stmt],
    seed_env: Option<&TypeEnv>,
) -> AnalysisOutput<ModuleInference> {
    let mut infer = Infer::new();
    let (inference, diagnostics) = infer.infer_program_collecting(program, seed_stmts, seed_env);
    if diagnostics.is_empty() {
        AnalysisOutput::success(inference)
    } else {
        AnalysisOutput::partial(
            inference,
            diagnostics
                .into_iter()
                .map(|err| CompilerDiagnostic::error(err.span, err.to_string()))
                .collect(),
        )
    }
}

fn lex_diagnostic(err: LexError) -> CompilerDiagnostic {
    let message = match err.kind {
        LexErrorKind::UnexpectedChar(c) => format!("unexpected character: '{}'", c),
        LexErrorKind::UnterminatedString => "unterminated string literal".to_string(),
        LexErrorKind::ReservedIdentifier => "reserved identifier".to_string(),
    };
    CompilerDiagnostic::error(Some(SourceSpan::from_lex_span(err.span)), message)
}

fn parse_diagnostic(err: ParseError) -> CompilerDiagnostic {
    CompilerDiagnostic::error(Some(SourceSpan::from_lex_span(err.span)), err.message)
}

fn reassoc_diagnostic(err: ReassocError) -> CompilerDiagnostic {
    CompilerDiagnostic::error(Some(err.span), err.message)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{DeriveTrait, ExprKind};
    use crate::syntax::{SyntaxDelimiter, SyntaxTemplate, SyntaxToken};

    #[test]
    fn parse_source_reports_lex_span() {
        let err = parse_source("@").expect_err("reserved operator should fail lexing");
        let span = err.span.expect("lex diagnostic should include a span");

        assert_eq!(span.start_line, 1);
        assert_eq!(span.start_col, 1);
    }

    #[test]
    fn parse_source_reports_unicode_character_in_lex_errors() {
        let err = parse_source("fn café() { 1 }\n")
            .expect_err("non-ASCII identifier should fail lexing for now");

        assert_eq!(err.message, "unexpected character: 'é'");
    }

    #[test]
    fn pipeline_can_parse_reassociate_and_infer_source() {
        let mut program = parse_source("let x = 1;").expect("source should parse");
        reassociate_standalone(&mut program).expect("source should reassociate");
        let result = infer_program(&mut program).expect("source should infer");

        assert!(!program.stmts.is_empty());
        assert!(!result.expr_types.is_empty());
    }

    #[test]
    fn parse_source_preserves_parenthesized_grouping() {
        let program = parse_source("let x = (a ++ b);\n").expect("source should parse");
        let Stmt::Let { value, .. } = &program.stmts[0] else {
            panic!("expected let statement");
        };

        assert!(matches!(value.kind, ExprKind::Grouped(_)));
    }

    #[test]
    fn parse_source_preserves_syntax_quote_tree() {
        let program =
            parse_source("let syntax = '{foo(1, x + y)};\n").expect("source should parse");
        let Stmt::Let { value, .. } = &program.stmts[0] else {
            panic!("expected let statement");
        };
        let ExprKind::SyntaxQuote(syntax) = &value.kind else {
            panic!("expected syntax quote expression");
        };
        let SyntaxTemplate::Tree {
            delimiter,
            children,
            ..
        } = syntax
        else {
            panic!("expected quoted brace tree");
        };

        assert_eq!(*delimiter, SyntaxDelimiter::Brace);
        assert_eq!(children.len(), 2);
        assert!(matches!(
            children[0],
            SyntaxTemplate::Token {
                token: SyntaxToken::Ident(ref name),
                ..
            } if name == "foo"
        ));
        assert!(matches!(
            children[1],
            SyntaxTemplate::Tree {
                delimiter: SyntaxDelimiter::Paren,
                ..
            }
        ));
    }

    #[test]
    fn parse_source_ignores_initial_hashbang() {
        let program =
            parse_source("#!/usr/bin/env hern\nlet x = 1;\n").expect("source should parse");
        let span = program.stmts[0].span();

        assert_eq!(span.start_line, 2);
        assert_eq!(span.start_col, 1);
    }

    #[test]
    fn parse_source_accepts_type_derives() {
        let program =
            parse_source("#[derive(Default, Eq, Ord, ToString)]\ntype Box('a) = Box('a)\n")
                .expect("source should parse");
        let Stmt::Type(type_def) = &program.stmts[0] else {
            panic!("expected type definition");
        };

        assert_eq!(type_def.derives.len(), 1);
        assert_eq!(
            type_def.derives[0].traits,
            vec![
                DeriveTrait::Default,
                DeriveTrait::Eq,
                DeriveTrait::Ord,
                DeriveTrait::ToString
            ]
        );
    }

    #[test]
    fn parse_source_reports_missing_type_rhs_before_next_statement() {
        let err = parse_source("type Empty =\nlet x = 1\n")
            .expect_err("missing type rhs should fail parsing");

        assert_eq!(
            err.message,
            "expected type or variant after `=` in type declaration"
        );
        assert_eq!(err.span.expect("parse diagnostic span").start_line, 2);
    }

    #[test]
    fn recovering_parse_does_not_scavenge_statement_after_missing_type_rhs() {
        let parsed =
            parse_source_recovering("type Empty =\nlet x = 1;\n").expect("source should lex");

        assert_eq!(parsed.diagnostics.len(), 1);
        assert_eq!(
            parsed.diagnostics[0].message,
            "expected type or variant after `=` in type declaration"
        );
        assert_eq!(parsed.program.stmts.len(), 1);
    }

    #[test]
    fn parse_source_reports_missing_let_rhs_before_next_statement() {
        let err =
            parse_source("let x =\nlet y = 1;\n").expect_err("missing let rhs should fail parsing");

        assert_eq!(err.message, "expected expression after `=` in let binding");
        assert_eq!(err.span.expect("parse diagnostic span").start_line, 2);
    }

    #[test]
    fn parse_source_rejects_unknown_derives() {
        let err = parse_source("#[derive(Clone)]\ntype Box('a) = Box('a)\n")
            .expect_err("unknown derive should fail");

        assert!(err.message.contains("Cannot derive `Clone`"));
    }

    #[test]
    fn parse_source_accepts_test_blocks_with_marked_tests() {
        let program =
            parse_source("test { #[test] fn works() { () } }\n").expect("test block should parse");
        let Stmt::TestBlock { stmts, .. } = &program.stmts[0] else {
            panic!("expected test block");
        };
        assert_eq!(stmts.len(), 1);
        assert!(stmts[0].is_test_fn());
    }

    #[test]
    fn parse_source_records_declaration_spans() {
        let program = parse_source("fn answer() { 42 }\n").expect("source should parse");
        let span = program.stmts[0].span();

        assert_eq!(span.start_line, 1);
        assert_eq!(span.start_col, 1);
        assert!(span.end_col > span.start_col);
    }

    #[test]
    fn recovering_parse_reports_multiple_parse_errors() {
        let parsed = parse_source_recovering("let a = ;\nlet b = ;\n").expect("source should lex");

        assert_eq!(parsed.program.stmts.len(), 0);
        assert_eq!(parsed.diagnostics.len(), 2);
        assert_eq!(
            parsed.diagnostics[0].span.expect("first span").start_line,
            1
        );
        assert_eq!(
            parsed.diagnostics[1].span.expect("second span").start_line,
            2
        );
    }

    #[test]
    fn parse_diagnostics_render_source_tokens_not_debug_names() {
        let err = parse_source("fn (x) { x }\n").expect_err("source should fail parsing");

        assert_eq!(err.message, "Expected identifier, found `(`");
    }

    #[test]
    fn collecting_inference_reports_independent_top_level_type_errors() {
        let mut program =
            parse_source("let a: bool = 1;\nlet b: bool = 2;\n").expect("source should parse");
        reassociate_standalone(&mut program).expect("source should reassociate");

        let output = infer_program_collecting(&mut program);
        let inference = output
            .value
            .expect("collecting inference should return partial state");

        assert_eq!(output.diagnostics.len(), 2);
        assert_eq!(
            output
                .diagnostics
                .iter()
                .map(|diagnostic| diagnostic.span.expect("type error span").start_line)
                .collect::<Vec<_>>(),
            vec![1, 2]
        );
        assert!(inference.env.get("a").is_none());
        assert!(inference.env.get("b").is_none());
    }

    #[test]
    fn collecting_inference_skips_dependent_top_level_declarations() {
        let mut program =
            parse_source("let bad: bool = 1;\nlet dependent = bad;\nlet other_bad: bool = 2;\n")
                .expect("source should parse");
        reassociate_standalone(&mut program).expect("source should reassociate");

        let output = infer_program_collecting(&mut program);
        let inference = output
            .value
            .expect("collecting inference should return partial state");

        assert_eq!(output.diagnostics.len(), 2);
        assert_eq!(
            output
                .diagnostics
                .iter()
                .map(|diagnostic| diagnostic.span.expect("type error span").start_line)
                .collect::<Vec<_>>(),
            vec![1, 3]
        );
        assert!(inference.env.get("bad").is_none());
        assert!(inference.env.get("dependent").is_none());
        assert!(inference.env.get("other_bad").is_none());
    }

    #[test]
    fn collecting_inference_reports_bad_function_body_and_later_independent_error() {
        let mut program = parse_source("fn bad() -> bool { 1 }\nlet other: bool = 2;\n")
            .expect("source should parse");
        reassociate_standalone(&mut program).expect("source should reassociate");

        let output = infer_program_collecting(&mut program);
        let inference = output
            .value
            .expect("collecting inference should return partial state");

        assert_eq!(output.diagnostics.len(), 2);
        assert_eq!(
            output
                .diagnostics
                .iter()
                .map(|diagnostic| diagnostic.span.expect("type error span").start_line)
                .collect::<Vec<_>>(),
            vec![1, 2]
        );
        assert!(inference.env.get("bad").is_none());
        assert!(inference.env.get("other").is_none());
    }

    #[test]
    fn collecting_inference_keeps_legacy_dot_trait_uses_independent_of_failed_impls() {
        let mut program = parse_source(
            "trait Pair 'a {\n    fn combine(lhs: 'a, rhs: 'a) -> 'a\n}\n\
             impl Pair for float {\n    fn combine(lhs) { lhs }\n}\n\
             let via_trait = Pair.combine(1, 2);\nlet other: bool = 2;\n",
        )
        .expect("source should parse");
        reassociate_standalone(&mut program).expect("source should reassociate");

        let output = infer_program_collecting(&mut program);
        let inference = output
            .value
            .expect("collecting inference should return partial state");

        assert_eq!(output.diagnostics.len(), 3);
        assert_eq!(
            output
                .diagnostics
                .iter()
                .map(|diagnostic| diagnostic.span.expect("type error span").start_line)
                .collect::<Vec<_>>(),
            vec![5, 7, 8]
        );
        assert!(inference.env.get("via_trait").is_none());
        assert!(inference.env.get("other").is_none());
    }

    #[test]
    fn trait_methods_must_mention_trait_parameter() {
        let mut program = parse_source("trait Ping 'a {\n    fn ping() -> string\n}\n")
            .expect("source should parse");
        reassociate_standalone(&mut program).expect("source should reassociate");

        let output = infer_program_collecting(&mut program);

        assert!(output.value.is_some());
        assert_eq!(output.diagnostics.len(), 1);
        assert!(
            output.diagnostics[0]
                .message
                .contains("must mention a trait parameter")
        );
    }
}
