use super::expand::{
    MacroExecutionOptions, expand_macros, expand_macros_with_fuel, expand_macros_with_limits,
    macro_expansion_cache_key,
};
use crate::ast::{ExprKind, SourceSpan, Stmt};
use crate::pipeline::{infer_program, parse_source};

fn expand_diagnostic(source: &str) -> crate::analysis::CompilerDiagnostic {
    let mut program = parse_source(source).expect("source should parse");
    expand_macros(&mut program).expect_err("macro expansion should fail")
}

fn expand_error(source: &str) -> String {
    expand_diagnostic(source).message
}

#[test]
fn duplicate_macro_definition_is_rejected() {
    let message = expand_error(
        r#"
macro twice(input: Syntax) -> MacroResult(Syntax) { Ok(input) }
macro twice(input: Syntax) -> MacroResult(Syntax) { Ok(input) }
"#,
    );

    assert!(
        message.contains("duplicate macro `twice`"),
        "unexpected diagnostic: {message}"
    );
}

#[test]
fn unknown_macro_call_is_rejected() {
    let message = expand_error("missing!(1);\n");

    assert!(
        message.contains("unknown macro `missing!`"),
        "unexpected diagnostic: {message}"
    );
}

#[test]
fn recursive_macro_expansion_stops_at_fuel_limit() {
    let mut program = parse_source(
        r#"
macro again(input: Syntax) -> MacroResult(Syntax) {
  Ok(input)
}

again!(1);
"#,
    )
    .expect("source should parse");
    let message = expand_macros_with_fuel(&mut program, 0)
        .expect_err("macro expansion should fail")
        .message;

    assert!(
        message.contains("macro expansion fuel exhausted"),
        "unexpected diagnostic: {message}"
    );
}

#[test]
fn macro_expansion_cache_key_changes_with_input_syntax() {
    let program = parse_source(
        r#"
macro id(input: Syntax) -> MacroResult(Syntax) { Ok(input) }
id!(1);
id!(2);
"#,
    )
    .expect("source should parse");
    let Stmt::Macro(def) = &program.stmts[0] else {
        panic!("expected macro definition");
    };
    let inputs = program.stmts[1..]
        .iter()
        .map(|stmt| {
            let Stmt::Expr(expr) = stmt else {
                panic!("expected macro call statement");
            };
            let ExprKind::MacroCall { input, .. } = &expr.kind else {
                panic!("expected macro call expression");
            };
            input
        })
        .collect::<Vec<_>>();

    let first = macro_expansion_cache_key(def, inputs[0]);
    let second = macro_expansion_cache_key(def, inputs[1]);

    assert_eq!(first.macro_definition_hash, second.macro_definition_hash);
    assert_ne!(first.macro_input_hash, second.macro_input_hash);
}

#[test]
fn macro_expansion_cache_key_changes_with_macro_definition() {
    let program = parse_source(
        r#"
macro first(input: Syntax) -> MacroResult(Syntax) { Ok(input) }
macro second(input: Syntax) -> MacroResult(Syntax) { Ok('{ 2 }) }
first!(1);
"#,
    )
    .expect("source should parse");
    let Stmt::Macro(first_def) = &program.stmts[0] else {
        panic!("expected first macro definition");
    };
    let Stmt::Macro(second_def) = &program.stmts[1] else {
        panic!("expected second macro definition");
    };
    let Stmt::Expr(expr) = &program.stmts[2] else {
        panic!("expected macro call statement");
    };
    let ExprKind::MacroCall { input, .. } = &expr.kind else {
        panic!("expected macro call expression");
    };

    let first = macro_expansion_cache_key(first_def, input);
    let second = macro_expansion_cache_key(second_def, input);

    assert_ne!(first.macro_definition_hash, second.macro_definition_hash);
    assert_eq!(first.macro_input_hash, second.macro_input_hash);
    assert_eq!(first.macro_prelude_hash, second.macro_prelude_hash);
    assert_eq!(first.compiler_abi_hash, second.compiler_abi_hash);
}

#[test]
fn top_level_macro_call_can_expand_to_items() {
    let mut program = parse_source(
        r#"
macro make_fn(input: Syntax) -> MacroResult(Syntax) {
  Ok(syntax_sequence(syntax_children('{ fn generated() { 41 } })))
}

make_fn!(());
generated()
"#,
    )
    .expect("source should parse");

    expand_macros(&mut program).expect("macro expansion should succeed");

    assert!(
        program
            .stmts
            .iter()
            .any(|stmt| matches!(stmt, crate::ast::Stmt::Fn { name, .. } if name == "generated")),
        "item macro should insert generated function: {:?}",
        program.stmts
    );
}

#[test]
fn top_level_function_attribute_macro_can_replace_target() {
    let mut program = parse_source(
        r#"
macro rename(input: Syntax) -> MacroResult(Syntax) {
  match input {
    '{ fn $name:ident() $body:block } ->
      Ok(syntax_sequence(syntax_children('{ fn wrapped() $body }))),
    _ -> Err(MacroError("rename expects a function")),
  }
}

#[rename]
fn original() { 42 }

wrapped()
"#,
    )
    .expect("source should parse");

    expand_macros(&mut program).expect("macro expansion should succeed");

    assert!(
        program
            .stmts
            .iter()
            .any(|stmt| matches!(stmt, crate::ast::Stmt::Fn { name, .. } if name == "wrapped")),
        "attribute macro should replace the target function: {:?}",
        program.stmts
    );
    assert!(
        !program
            .stmts
            .iter()
            .any(|stmt| matches!(stmt, crate::ast::Stmt::Fn { name, .. } if name == "original")),
        "attribute macro should remove the original target function: {:?}",
        program.stmts
    );
}

#[test]
fn custom_derive_macro_can_append_items_for_type_target() {
    let mut program = parse_source(
        r#"
macro derive_Label(input: Syntax) -> MacroResult(Syntax) {
  match input {
    '{ type $name:ident = $variant:ident } ->
      Ok(syntax_sequence(syntax_children('{
        impl ToString for $name {
          fn to_string(self) { "labelled" }
        }
      }))),
    _ -> Err(MacroError("derive_Label expects a simple sum type")),
  }
}

#[derive(Label)]
type Labelled = Labelled
"#,
    )
    .expect("source should parse");

    expand_macros(&mut program).expect("macro expansion should succeed");

    assert!(
        program
            .stmts
            .iter()
            .any(|stmt| matches!(stmt, crate::ast::Stmt::Type(type_def) if type_def.name == "Labelled" && type_def.derives.is_empty())),
        "custom derive should consume the derive metadata from the target type: {:?}",
        program.stmts
    );
    assert!(
        program.stmts.iter().any(
            |stmt| matches!(stmt, crate::ast::Stmt::Impl(impl_def) if impl_def.trait_name == "ToString")
        ),
        "custom derive should append generated items: {:?}",
        program.stmts
    );
}

#[test]
fn invalid_expanded_expression_is_rejected() {
    let diagnostic = expand_diagnostic(
        r#"
macro bad(input: Syntax) -> MacroResult(Syntax) {
  Ok('{ if })
}

bad!(1);
"#,
    );
    let message = diagnostic.message;

    assert!(
        message.contains("expansion did not produce an expression"),
        "unexpected diagnostic: {message}"
    );
    assert!(
        message.contains("macro `bad`"),
        "unexpected diagnostic: {message}"
    );
    assert!(
        message.contains("macro definition starts at"),
        "unexpected diagnostic: {message}"
    );
    assert!(
        message.contains("generated source:\n{if}"),
        "unexpected diagnostic: {message}"
    );
    assert!(
        message.contains("syntax origin: generated syntax"),
        "unexpected diagnostic: {message}"
    );
    assert_eq!(
        diagnostic.span,
        Some(SourceSpan {
            start_line: 6,
            start_col: 1,
            end_line: 6,
            end_col: 8,
        })
    );
}

#[test]
fn parse_back_failure_reports_spliced_source_origin() {
    let diagnostic = expand_diagnostic(
        r#"
macro bad(input: Syntax) -> MacroResult(Syntax) {
  Ok(input)
}

bad!(if);
"#,
    );
    let message = diagnostic.message;

    assert!(
        message.contains("syntax origin: source syntax at 6:5-6:9 (tree:paren)"),
        "unexpected diagnostic: {message}"
    );
    assert!(
        message.contains("macro `bad` expansion did not produce an expression"),
        "unexpected diagnostic: {message}"
    );
    assert!(
        message.contains("macro definition starts at 2:1"),
        "unexpected diagnostic: {message}"
    );
    assert!(
        message.contains("generated source:\n(if)"),
        "unexpected diagnostic: {message}"
    );
    assert_eq!(
        diagnostic.span,
        Some(SourceSpan {
            start_line: 6,
            start_col: 1,
            end_line: 6,
            end_col: 9,
        })
    );
    assert!(
        diagnostic
            .related
            .iter()
            .any(|related| related.message == "while expanding `bad!` here"
                && related.span
                    == SourceSpan {
                        start_line: 6,
                        start_col: 1,
                        end_line: 6,
                        end_col: 9,
                    }),
        "call-site expansion related information missing: {:?}",
        diagnostic.related
    );
    assert!(
        diagnostic
            .related
            .iter()
            .any(|related| related.message == "macro `bad` is defined here"
                && related.span
                    == SourceSpan {
                        start_line: 2,
                        start_col: 1,
                        end_line: 4,
                        end_col: 2,
                    }),
        "definition expansion related information missing: {:?}",
        diagnostic.related
    );
}

#[test]
fn expanded_expression_rejects_trailing_tokens() {
    let message = expand_error(
        r##"
macro bad(input: Syntax) -> MacroResult(Syntax) {
  Ok(syntax_sequence([syntax_literal("1"), syntax_literal("2")]))
}

bad!(());
"##,
    );

    assert!(
        message.contains("unexpected token after syntax expression"),
        "unexpected diagnostic: {message}"
    );
    assert!(
        message.contains("macro `bad`"),
        "unexpected diagnostic: {message}"
    );
    assert!(
        message.contains("generated source:\n1 2"),
        "unexpected diagnostic: {message}"
    );
}

#[test]
fn macro_runtime_failure_includes_related_expansion_context() {
    let diagnostic = expand_diagnostic(
        r##"
macro bad(input: Syntax) -> MacroResult(Syntax) {
  Ok(syntax_children("not syntax"))
}

bad!(ignored);
"##,
    );
    let message = diagnostic.message;

    assert!(
        message.contains("macro `bad!`: syntax_children expects Syntax"),
        "unexpected diagnostic: {message}"
    );
    assert!(
        diagnostic
            .related
            .iter()
            .any(|related| related.message == "while expanding `bad!` here"
                && related.span
                    == SourceSpan {
                        start_line: 6,
                        start_col: 1,
                        end_line: 6,
                        end_col: 14,
                    }),
        "call-site expansion related information missing: {:?}",
        diagnostic.related
    );
    assert!(
        diagnostic
            .related
            .iter()
            .any(|related| related.message == "macro `bad` is defined here"
                && related.span
                    == SourceSpan {
                        start_line: 2,
                        start_col: 1,
                        end_line: 4,
                        end_col: 2,
                    }),
        "definition expansion related information missing: {:?}",
        diagnostic.related
    );
}

#[test]
fn macro_non_exhaustive_match_notes_relevant_quote_pattern_arm() {
    let diagnostic = expand_diagnostic(
        r##"
macro only_ident(input: Syntax) -> MacroResult(Syntax) {
  match input {
    '{$name:ident} -> Ok(input),
  }
}

only_ident!(1 + 2);
"##,
    );
    let message = diagnostic.message;

    assert!(
        message.contains("macro `only_ident!`: non-exhaustive macro match"),
        "unexpected diagnostic: {message}"
    );
    assert!(
        diagnostic.related.iter().any(|related| related.message
            == "relevant macro pattern arm is here"
            && related.span.start_line == 4),
        "quote-pattern related information missing: {:?}",
        diagnostic.related
    );
}

#[test]
fn expanded_type_error_includes_macro_context() {
    let mut program = parse_source(
        r#"
macro bad(input: Syntax) -> MacroResult(Syntax) {
  Ok('{ if true { 1 } else { false } })
}

bad!(());
"#,
    )
    .expect("source should parse");
    expand_macros(&mut program).expect("macro expansion should succeed");
    program
        .stmts
        .retain(|stmt| !matches!(stmt, crate::ast::Stmt::Macro(_)));
    let diagnostic = infer_program(&mut program).expect_err("expanded code should fail to infer");

    assert!(
        diagnostic.message.contains("while expanding `bad!` here"),
        "unexpected diagnostic: {}",
        diagnostic.message
    );
    assert!(
        diagnostic.message.contains("macro definition starts at"),
        "unexpected diagnostic: {}",
        diagnostic.message
    );
    assert!(
        diagnostic.message.contains("generated source:"),
        "unexpected diagnostic: {}",
        diagnostic.message
    );
    assert!(
        diagnostic
            .related
            .iter()
            .any(|related| related.message == "while expanding `bad!` here"
                && related.span
                    == SourceSpan {
                        start_line: 6,
                        start_col: 1,
                        end_line: 6,
                        end_col: 9,
                    }),
        "call-site expansion related information missing: {:?}",
        diagnostic.related
    );
    assert!(
        diagnostic
            .related
            .iter()
            .any(|related| related.message == "macro `bad` is defined here"
                && related.span
                    == SourceSpan {
                        start_line: 2,
                        start_col: 1,
                        end_line: 4,
                        end_col: 2,
                    }),
        "definition expansion related information missing: {:?}",
        diagnostic.related
    );
}

#[test]
fn expanded_type_error_preserves_spliced_source_span() {
    let mut program = parse_source(
        r#"
macro id(input: Syntax) -> MacroResult(Syntax) {
  Ok(input)
}

let value: bool = id!(1);
"#,
    )
    .expect("source should parse");
    expand_macros(&mut program).expect("macro expansion should succeed");
    program
        .stmts
        .retain(|stmt| !matches!(stmt, crate::ast::Stmt::Macro(_)));
    let diagnostic = infer_program(&mut program).expect_err("expanded code should fail to infer");

    assert!(
        diagnostic.message.contains("expected `bool`, got `int`"),
        "unexpected diagnostic: {}",
        diagnostic.message
    );
    assert_eq!(
        diagnostic.span,
        Some(crate::ast::SourceSpan {
            start_line: 6,
            start_col: 23,
            end_line: 6,
            end_col: 24,
        })
    );
}

#[test]
fn unsupported_macro_phase_expression_is_rejected_during_lowering() {
    let message = expand_error(
        r#"
macro bad(input: Syntax) -> MacroResult(Syntax) {
  let xs = [];
  Ok([..xs])
}

bad!(1);
"#,
    );

    assert!(
        message.contains("unsupported array spread in macro body"),
        "unexpected diagnostic: {message}"
    );
}

#[test]
fn unsupported_macro_phase_assignment_target_is_rejected() {
    let message = expand_error(
        r#"
macro bad(input: Syntax) -> MacroResult(Syntax) {
  let r = #{ x: input };
  r.x = input;
  Ok(input)
}

bad!(1);
"#,
    );

    assert!(
        message.contains("unsupported assignment target in macro body"),
        "unexpected diagnostic: {message}"
    );
}

#[test]
fn comptime_runtime_step_limit_is_enforced() {
    let mut program = parse_source(
        r#"
macro id(input: Syntax) -> MacroResult(Syntax) {
  Ok(input)
}

id!(1);
"#,
    )
    .expect("source should parse");
    let message = expand_macros_with_limits(
        &mut program,
        MacroExecutionOptions {
            max_eval_steps: 1,
            ..MacroExecutionOptions::default()
        },
    )
    .expect_err("macro expansion should fail")
    .message;

    assert!(
        message.contains("macro comptime step limit exceeded"),
        "unexpected diagnostic: {message}"
    );
}

#[test]
fn comptime_runtime_output_syntax_limit_is_enforced() {
    let mut program = parse_source(
        r#"
macro id(input: Syntax) -> MacroResult(Syntax) {
  Ok(input)
}

id!(1 + 2);
"#,
    )
    .expect("source should parse");
    let message = expand_macros_with_limits(
        &mut program,
        MacroExecutionOptions {
            max_output_syntax_nodes: 1,
            ..MacroExecutionOptions::default()
        },
    )
    .expect_err("macro expansion should fail")
    .message;

    assert!(
        message.contains("macro generated too much syntax"),
        "unexpected diagnostic: {message}"
    );
}

#[test]
fn recursive_macro_expansion_uses_expansion_limit() {
    let mut program = parse_source(
        r#"
macro id(input: Syntax) -> MacroResult(Syntax) {
  Ok(input)
}

id!(id!(1));
"#,
    )
    .expect("source should parse");
    let message = expand_macros_with_limits(
        &mut program,
        MacroExecutionOptions {
            max_expansions: 1,
            ..MacroExecutionOptions::default()
        },
    )
    .expect_err("macro expansion should fail")
    .message;

    assert!(
        message.contains("macro expansion fuel exhausted"),
        "unexpected diagnostic: {message}"
    );
}

#[test]
fn comptime_runtime_call_depth_limit_is_enforced() {
    let mut program = parse_source(
        r#"
fn recur(input: Syntax) -> Syntax {
  recur(input)
}

macro boom(input: Syntax) -> MacroResult(Syntax) {
  Ok(recur(input))
}

boom!(1);
"#,
    )
    .expect("source should parse");
    let message = expand_macros_with_limits(
        &mut program,
        MacroExecutionOptions {
            max_call_depth: 1,
            ..MacroExecutionOptions::default()
        },
    )
    .expect_err("macro expansion should fail")
    .message;

    assert!(
        message.contains("macro comptime call depth limit exceeded"),
        "unexpected diagnostic: {message}"
    );
}

#[test]
fn comptime_generated_source_limit_is_enforced() {
    let mut program = parse_source(
        r#"
macro id(input: Syntax) -> MacroResult(Syntax) {
  Ok(input)
}

id!(long_identifier_name);
"#,
    )
    .expect("source should parse");
    let message = expand_macros_with_limits(
        &mut program,
        MacroExecutionOptions {
            max_generated_source_bytes: 4,
            ..MacroExecutionOptions::default()
        },
    )
    .expect_err("macro expansion should fail")
    .message;

    assert!(
        message.contains("generated too much source"),
        "unexpected diagnostic: {message}"
    );
}
