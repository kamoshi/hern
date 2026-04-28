use crate::analysis::CompilerDiagnostic;
use crate::ast::{Program, SourceSpan, Stmt};
use crate::lex::error::{LexError, LexErrorKind, ParseError};
use crate::lex::{Lexer, Spanned};
use crate::parse::Parser;
use crate::reassoc::{build_fixity_table, reassoc_program};
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

pub fn reassociate_with_program(program: &mut Program, fixity_source: &Program) {
    let mut fixity = build_fixity_table(fixity_source);
    fixity.extend(build_fixity_table(program));
    reassoc_program(program, &fixity);
}

pub fn reassociate_standalone(program: &mut Program) {
    let fixity = build_fixity_table(program);
    reassoc_program(program, &fixity);
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
        LexErrorKind::UnexpectedChar(c) => {
            format!("unexpected character: '{}'", c as char)
        }
        LexErrorKind::UnterminatedString => "unterminated string literal".to_string(),
        LexErrorKind::ReservedIdentifier => "reserved identifier".to_string(),
    };
    CompilerDiagnostic::error(Some(SourceSpan::from_lex_span(err.span)), message)
}

fn parse_diagnostic(err: ParseError) -> CompilerDiagnostic {
    CompilerDiagnostic::error(Some(SourceSpan::from_lex_span(err.span)), err.message)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_source_reports_lex_span() {
        let err = parse_source("@").expect_err("reserved operator should fail lexing");
        let span = err.span.expect("lex diagnostic should include a span");

        assert_eq!(span.start_line, 1);
        assert_eq!(span.start_col, 1);
    }

    #[test]
    fn pipeline_can_parse_reassociate_and_infer_source() {
        let mut program = parse_source("let x = 1;").expect("source should parse");
        reassociate_standalone(&mut program);
        let result = infer_program(&mut program).expect("source should infer");

        assert!(!program.stmts.is_empty());
        assert!(!result.expr_types.is_empty());
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
    fn collecting_inference_reports_independent_top_level_type_errors() {
        let mut program =
            parse_source("let a: bool = 1;\nlet b: bool = 2;\n").expect("source should parse");
        reassociate_standalone(&mut program);

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
        reassociate_standalone(&mut program);

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
        reassociate_standalone(&mut program);

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
    fn collecting_inference_avoids_trait_impl_cascades() {
        let mut program = parse_source(
            "trait Pair 'a {\n    fn combine(lhs: 'a, rhs: 'a) -> 'a\n}\n\
             impl Pair for f64 {\n    fn combine(lhs) { lhs }\n}\n\
             let via_trait = Pair.combine(1, 2);\nlet other: bool = 2;\n",
        )
        .expect("source should parse");
        reassociate_standalone(&mut program);

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
            vec![5, 8]
        );
        assert!(inference.env.get("via_trait").is_some());
        assert!(inference.env.get("other").is_none());
    }
}
