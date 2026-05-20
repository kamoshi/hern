use super::expand::{
    MacroExecutionOptions, expand_macros, expand_macros_with_fuel, expand_macros_with_limits,
};
use crate::pipeline::parse_source;

fn expand_error(source: &str) -> String {
    let mut program = parse_source(source).expect("source should parse");
    expand_macros(&mut program)
        .expect_err("macro expansion should fail")
        .message
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
fn invalid_expanded_expression_is_rejected() {
    let message = expand_error(
        r#"
macro bad(input: Syntax) -> MacroResult(Syntax) {
  Ok('{ if })
}

bad!(1);
"#,
    );

    assert!(
        message.contains("macro expansion did not produce an expression"),
        "unexpected diagnostic: {message}"
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
        message.contains("macro generated too much source"),
        "unexpected diagnostic: {message}"
    );
}
