//! End-to-end inference tests for whole source snippets.
//!
//! These tests exercise the public inference surface across language features.
//! Focused unit tests should live beside the module that owns the specific rule.

use super::*;
use crate::pipeline::{parse_source, reassociate_standalone};

#[test]
fn failed_type_declaration_prunes_variant_state() {
    let mut program =
        parse_source("type Broken('a) = Good('a) | Bad(Missing)\n").expect("source should parse");
    reassociate_standalone(&mut program).expect("source should reassociate");

    let mut infer = Infer::new();
    let (inference, diagnostics) = infer.infer_program_collecting(&mut program, &[], None);

    assert_eq!(diagnostics.len(), 1);
    assert!(matches!(
        diagnostics[0].error.as_ref(),
        TypeError::UnknownType(name) if name == "Missing"
    ));
    assert_eq!(diagnostics[0].span.expect("type error span").start_line, 1);
    assert!(!infer.types.declared.contains("Broken"));
    assert!(!infer.types.variant_env.0.contains_key("Good"));
    assert!(!infer.types.variant_env.0.contains_key("Bad"));
    assert!(inference.env.get("Good").is_none());
    assert!(inference.env.get("Bad").is_none());
}

#[test]
fn collecting_inference_skips_nested_pattern_references_to_unavailable_variants() {
    let mut program = parse_source(
        "type Broken('a) = Good('a) | Bad(Missing)\n\
         fn dependent(xs) { match xs { [(Good(x), y)] -> x, _ -> 0 } }\n\
         let other: bool = 1;\n",
    )
    .expect("source should parse");
    reassociate_standalone(&mut program).expect("source should reassociate");

    let mut infer = Infer::new();
    let (inference, diagnostics) = infer.infer_program_collecting(&mut program, &[], None);

    assert_eq!(
        diagnostics.len(),
        2,
        "dependent nested pattern should be skipped, not diagnosed again"
    );
    assert!(diagnostics.iter().any(|diagnostic| matches!(
        diagnostic.error.as_ref(),
        TypeError::UnknownType(name) if name == "Missing"
    )));
    assert!(diagnostics.iter().any(|diagnostic| matches!(
        diagnostic.error.as_ref(),
        TypeError::Mismatch {
            expected: Ty::Con(name),
            got: Ty::Int,
        } if name == "bool"
    )));
    assert_eq!(
        diagnostics
            .iter()
            .map(|diagnostic| diagnostic.span.expect("type error span").start_line)
            .collect::<Vec<_>>(),
        vec![1, 3]
    );
    assert!(inference.env.get("dependent").is_none());
    assert!(inference.env.get("other").is_none());
}

#[test]
fn collecting_inference_reports_independent_test_block_errors() {
    let mut program = parse_source(
        "test {
           #[test]
           fn has_arg(x: int) { () }

           #[test]
           fn returns_int() { 1 }
         }\n",
    )
    .expect("source should parse");
    reassociate_standalone(&mut program).expect("source should reassociate");

    let mut infer = Infer::new();
    let (_, diagnostics) = infer.infer_program_collecting(&mut program, &[], None);

    assert_eq!(diagnostics.len(), 2);
    assert!(matches!(
        diagnostics[0].error.as_ref(),
        TypeError::InvalidTestFunction { name, message }
            if name == "has_arg" && message.contains("expected no parameters")
    ));
    assert_eq!(diagnostics[0].span.expect("type error span").start_line, 3);
    assert!(matches!(
        diagnostics[1].error.as_ref(),
        TypeError::InvalidTestFunction { name, message }
            if name == "returns_int" && message.contains("expected return type unit")
    ));
    assert_eq!(diagnostics[1].span.expect("type error span").start_line, 6);
}

#[test]
fn collecting_inference_reports_all_duplicate_test_names() {
    let mut program = parse_source(
        "test {
           #[test]
           fn same() { () }

           #[test]
           fn same() { () }

           #[test]
           fn same() { () }
         }\n",
    )
    .expect("source should parse");
    reassociate_standalone(&mut program).expect("source should reassociate");

    let (_, diagnostics) = Infer::new().infer_program_collecting(&mut program, &[], None);

    let duplicates = diagnostics
        .iter()
        .filter(|diagnostic| matches!(diagnostic.error.as_ref(), TypeError::DuplicateTestFunction(name) if name == "same"))
        .count();
    assert_eq!(duplicates, 2);
}

#[test]
fn macro_phase_inference_records_metadata_after_unrelated_error() {
    let mut program = parse_source(
        "type Syntax = Dummy
         type Result('a, 'e) = Ok('a) | Err('e)
         type MacroError = MacroError(string)
         type alias MacroResult('a) = Result('a, MacroError)
         macro rewrite(input: Syntax) -> MacroResult(Syntax) {
           match input {
             '{$lhs:expr + $rhs:expr} -> Ok('{ $lhs }),
             _ -> Err(MacroError(\"bad\")),
           }
         }
         let unrelated: bool = 1;
        ",
    )
    .expect("source should parse");
    reassociate_standalone(&mut program).expect("source should reassociate");

    let input_span = match program
        .stmts
        .iter()
        .find(|stmt| matches!(stmt, Stmt::Macro(_)))
    {
        Some(Stmt::Macro(def)) => def.param_span,
        _ => panic!("expected macro definition"),
    };

    let mut infer = Infer::new();
    let (inference, diagnostics) = infer.infer_program_collecting(&mut program, &[], None);

    assert_eq!(diagnostics.len(), 1);
    assert!(matches!(
        diagnostics[0].error.as_ref(),
        TypeError::Mismatch {
            expected: Ty::Con(name),
            got: Ty::Int,
        } if name == "bool"
    ));
    assert_eq!(
        inference.binding_types.get(&input_span),
        Some(&Ty::Con("Syntax".to_string()))
    );
    assert!(
        inference
            .syntax_captures
            .values()
            .any(|capture| capture.name == "lhs" && !capture.repeat),
        "macro syntax capture metadata should survive unrelated errors: {:?}",
        inference.syntax_captures
    );
}

#[test]
fn macro_phase_rejects_runtime_only_top_level_values() {
    let mut program = parse_source(
        "type Syntax = Dummy
         type Result('a, 'e) = Ok('a) | Err('e)
         type MacroError = MacroError(string)
         type alias MacroResult('a) = Result('a, MacroError)
         let runtime_value = 1;
         macro bad(input: Syntax) -> MacroResult(Syntax) {
           Ok(runtime_value)
         }
        ",
    )
    .expect("source should parse");
    reassociate_standalone(&mut program).expect("source should reassociate");

    let (_, diagnostics) = Infer::new().infer_program_collecting(&mut program, &[], None);

    assert_eq!(diagnostics.len(), 1);
    assert!(matches!(
        diagnostics[0].error.as_ref(),
        TypeError::UnboundVariable(name) if name == "runtime_value"
    ));
}

#[test]
fn macro_phase_allows_prior_function_helpers() {
    let mut program = parse_source(
        "type Syntax = Dummy
         type Result('a, 'e) = Ok('a) | Err('e)
         type MacroError = MacroError(string)
         type alias MacroResult('a) = Result('a, MacroError)
         fn id_syntax(input: Syntax) -> Syntax { input }
         macro ok(input: Syntax) -> MacroResult(Syntax) {
           Ok(id_syntax(input))
         }
        ",
    )
    .expect("source should parse");
    reassociate_standalone(&mut program).expect("source should reassociate");

    let (_, diagnostics) = Infer::new().infer_program_collecting(&mut program, &[], None);

    assert!(diagnostics.is_empty(), "{diagnostics:?}");
}

#[test]
fn macro_signature_errors_are_type_errors() {
    let mut program = parse_source(
        "type Syntax = Dummy
         type Result('a, 'e) = Ok('a) | Err('e)
         type MacroError = MacroError(string)
         type alias MacroResult('a) = Result('a, MacroError)
         macro wrong_param(input: int) -> MacroResult(Syntax) {
           Ok(input)
         }
         macro wrong_return(input: Syntax) -> Syntax {
           input
         }
         macro wrong_body(input: Syntax) -> MacroResult(Syntax) Ok(input)
        ",
    )
    .expect("source should parse");
    reassociate_standalone(&mut program).expect("source should reassociate");

    let (_, diagnostics) = Infer::new().infer_program_collecting(&mut program, &[], None);
    let messages: Vec<_> = diagnostics
        .iter()
        .map(|diagnostic| diagnostic.to_string())
        .collect();

    assert!(
        messages
            .iter()
            .any(|message| message.contains("input parameter must have type `Syntax`")),
        "{messages:?}"
    );
    assert!(
        messages
            .iter()
            .any(|message| message.contains("return type must be `MacroResult(Syntax)`")),
        "{messages:?}"
    );
    assert!(
        messages
            .iter()
            .any(|message| message.contains("body must be a block expression")),
        "{messages:?}"
    );
}

#[test]
fn collecting_inference_keeps_duplicate_test_names_when_prepass_fails() {
    let mut program = parse_source(
        "type alias Bad('a, 'a) = 'a

         test {
           #[test]
           fn same() { () }

           #[test]
           fn same() { () }
         }\n",
    )
    .expect("source should parse");
    reassociate_standalone(&mut program).expect("source should reassociate");

    let (_, diagnostics) = Infer::new().infer_program_collecting(&mut program, &[], None);

    assert!(diagnostics.iter().any(|diagnostic| {
        matches!(
            diagnostic.error.as_ref(),
            TypeError::DuplicateTestFunction(name) if name == "same"
        )
    }));
    assert!(diagnostics.iter().any(|diagnostic| {
        matches!(
            diagnostic.error.as_ref(),
            TypeError::DuplicateTypeParameter { owner, param }
                if owner == "Bad" && param == "'a"
        )
    }));
}

#[test]
fn collecting_inference_normalizes_failed_symbol_types_before_rollback() {
    let mut program = parse_source(
        "fn takes(x) { x }\n\
         if takes(1) { 0 } else { 1 }\n",
    )
    .expect("source should parse");
    reassociate_standalone(&mut program).expect("source should reassociate");

    let callee_id = match &program.stmts[1] {
        Stmt::Expr(expr) => match &expr.kind {
            ExprKind::If { cond, .. } => match &cond.kind {
                ExprKind::Call { callee, .. } => callee.id,
                _ => panic!("condition should be a call"),
            },
            _ => panic!("second statement should be an if expression"),
        },
        _ => panic!("second statement should be an expression"),
    };

    let mut infer = Infer::new();
    let (inference, diagnostics) = infer.infer_program_collecting(&mut program, &[], None);

    assert_eq!(diagnostics.len(), 1);
    let callee_ty = inference
        .symbol_types
        .get(&callee_id)
        .expect("failed call callee type should be retained");
    assert!(
        free_type_vars(callee_ty).is_empty(),
        "retained failed symbol type should be normalized, got {callee_ty}"
    );
    match callee_ty {
        Ty::Func(params, ret) => {
            assert_eq!(params.len(), 1);
            assert_eq!(params[0].ty, Ty::Int);
            assert_eq!(*ret.ty, Ty::Int);
        }
        other => panic!("callee should retain a function type, got {other}"),
    }
}

#[test]
fn same_name_single_constructor_type_is_nominal() {
    let mut program = parse_source(
        "type Wrap = Wrap(float)\n\
         impl Wrap {\n\
           fn unwrap(self) { match self { Wrap(value) -> value } }\n\
         }\n\
         let wrapped = Wrap(1.0);\n\
         let value = wrapped.unwrap();\n",
    )
    .expect("source should parse");
    reassociate_standalone(&mut program).expect("source should reassociate");

    assert!(matches!(
        &program.stmts[0],
        Stmt::Type(td) if td.name == "Wrap" && td.variants.len() == 1
    ));

    let mut infer = Infer::new();
    infer
        .infer_program(&mut program)
        .expect("same-name constructor should infer as a nominal type");
}

#[test]
fn recursive_type_alias_reports_error_instead_of_recursing() {
    let mut program = parse_source(
        "type alias A = B\n\
         type alias B = A\n\
         extern value: A = \"value\";\n",
    )
    .expect("source should parse");
    reassociate_standalone(&mut program).expect("source should reassociate");

    let mut infer = Infer::new();
    let err = infer
        .infer_program(&mut program)
        .expect_err("recursive aliases should be rejected");

    assert!(matches!(
        err.error.as_ref(),
        TypeError::RecursiveTypeAlias { name, cycle }
            if name == "A" && cycle == &vec!["A".to_string(), "B".to_string(), "A".to_string()]
    ));
    assert_eq!(
        err.to_string(),
        "recursive type alias cycle `A -> B -> A` is not supported; use a nominal type constructor instead"
    );
}

#[test]
fn duplicate_type_parameters_are_rejected_before_alias_substitution() {
    let mut program =
        parse_source("type alias Bad('a, 'a) = 'a\nextern value: Bad(int, string) = \"value\";\n")
            .expect("source should parse");
    reassociate_standalone(&mut program).expect("source should reassociate");

    let err = Infer::new()
        .infer_program(&mut program)
        .expect_err("duplicate type parameters should be rejected");

    assert!(matches!(
        err.error.as_ref(),
        TypeError::DuplicateTypeParameter { owner, param }
            if owner == "Bad" && param == "'a"
    ));
}

#[test]
fn type_alias_application_arity_is_checked_during_conversion() {
    let err = infer_source_error(
        "type alias Pair('a, 'b) = ('a, 'b)\nextern value: Pair(int) = \"value\";\n",
    );

    assert!(matches!(
        err.error.as_ref(),
        TypeError::TypeAliasArityMismatch {
            name,
            expected: 2,
            got: 1,
        } if name == "Pair"
    ));
}

#[test]
fn nominal_type_application_arity_is_checked_during_conversion() {
    let err = infer_source_error(
        "type Option('a) = Some('a) | None\nextern value: Option(int, string) = \"value\";\n",
    );

    assert!(matches!(
        err.error.as_ref(),
        TypeError::TypeConstructorArityMismatch {
            name,
            expected: 1,
            got: 2,
        } if name == "Option"
    ));
}

#[test]
fn primitive_type_application_arity_is_checked_during_conversion() {
    let err = infer_source_error("extern value: int(string) = \"value\";\n");

    assert!(matches!(
        err.error.as_ref(),
        TypeError::TypeConstructorArityMismatch {
            name,
            expected: 0,
            got: 1,
        } if name == "int"
    ));
}

#[test]
fn collecting_inference_does_not_mutate_failed_inherent_self_types() {
    let mut program = parse_source(
        "type Box = Box(int)\n\
         impl Box {\n\
           fn bad(self, other: Self) -> int { true }\n\
         }\n",
    )
    .expect("source should parse");
    reassociate_standalone(&mut program).expect("source should reassociate");

    let mut infer = Infer::new();
    let (_inference, diagnostics) = infer.infer_program_collecting(&mut program, &[], None);

    assert_eq!(diagnostics.len(), 1);
    let Stmt::InherentImpl(id) = &program.stmts[1] else {
        panic!("second statement should be an inherent impl");
    };
    let Some(Type::Ident(name)) = id.methods[0].params[1].ty.as_ref() else {
        panic!("failed inherent impl method should retain its original Self annotation");
    };
    assert_eq!(name, "Self");
}

#[test]
fn collecting_inference_does_not_partially_mutate_failed_inherent_impl() {
    let mut program = parse_source(
        "type Box = Box(int)\n\
         impl Box {\n\
           fn ok(self, other: Self) -> int { 1 }\n\
           fn bad(self, other: Self) -> int { true }\n\
         }\n",
    )
    .expect("source should parse");
    reassociate_standalone(&mut program).expect("source should reassociate");

    let mut infer = Infer::new();
    let (_inference, diagnostics) = infer.infer_program_collecting(&mut program, &[], None);

    assert_eq!(diagnostics.len(), 1);
    let Stmt::InherentImpl(id) = &program.stmts[1] else {
        panic!("second statement should be an inherent impl");
    };
    for method in &id.methods {
        let Some(Type::Ident(name)) = method.params[1].ty.as_ref() else {
            panic!("failed inherent impl should retain original Self annotations");
        };
        assert_eq!(name, "Self");
    }
}

#[test]
fn missing_primitive_trait_impl_is_rejected_during_inference() {
    let err = infer_source_error(
        "trait Show 'a {
           fn show(x: 'a) -> string
         }

         Show::show(1)\n",
    );

    assert!(matches!(
        err.error.as_ref(),
        TypeError::MissingTraitImpl {
            trait_name,
            impl_target,
        } if trait_name == "Show" && impl_target == "int"
    ));
}

#[test]
fn missing_custom_type_trait_impl_is_rejected_during_inference() {
    let err = infer_source_error(
        "type Boxed = Boxed(float)

         trait Show 'a {
           fn show(x: 'a) -> string
         }

         Show::show(Boxed(1.0))\n",
    );

    assert!(matches!(
        err.error.as_ref(),
        TypeError::MissingTraitImpl {
            trait_name,
            impl_target,
        } if trait_name == "Show" && impl_target == "Boxed"
    ));
}

#[test]
fn collecting_inference_does_not_use_failed_local_impl_dict() {
    let mut program = parse_source(
        "type Boxed = Boxed(float)

         trait Show 'a {
           fn show(x: 'a) -> string
         }

         impl Show for Boxed {
           fn show(x) { 1 }
         }

         Show::show(Boxed(1.0))\n",
    )
    .expect("source should parse");
    reassociate_standalone(&mut program).expect("source should reassociate");

    let mut infer = Infer::new();
    let (_inference, diagnostics) = infer.infer_program_collecting(&mut program, &[], None);

    assert!(diagnostics.iter().any(|diagnostic| {
        matches!(
            diagnostic.error.as_ref(),
            TypeError::MissingTraitImpl {
                trait_name,
                impl_target,
            } if trait_name == "Show" && impl_target == "Boxed"
        )
    }));
}

#[test]
fn missing_structural_tuple_component_impl_is_rejected_during_inference() {
    let err = infer_source_error(
        "type Boxed = Boxed(float)

         trait Eq 'a {
           fn infix 4 ==(lhs: 'a, rhs: 'a) -> bool
           fn infix 4 !=(lhs: 'a, rhs: 'a) -> bool
         }

         impl Eq for float {
           fn ==(lhs, rhs) { true }
           fn !=(lhs, rhs) { false }
         }

         fn bad(a: (Boxed, float), b: (Boxed, float)) -> bool {
           a == b
         }\n",
    );

    assert!(matches!(
        err.error.as_ref(),
        TypeError::MissingTraitImpl {
            trait_name,
            impl_target,
        } if trait_name == "Eq" && impl_target == "Boxed"
    ));
}

#[test]
fn available_concrete_trait_impl_resolves_to_checked_dict_ref() {
    let mut program = parse_source(
        "trait Show 'a {
           fn show(x: 'a) -> string
         }

         impl Show for float {
           fn show(x) { \"ok\" }
         }

         let x = 1.0;
         x.show()\n",
    )
    .expect("source should parse");
    reassociate_standalone(&mut program).expect("source should reassociate");

    let mut infer = Infer::new();
    infer
        .infer_program(&mut program)
        .expect("available concrete impl should infer");

    let Stmt::Expr(expr) = &program.stmts[3] else {
        panic!("fourth statement should be the call expression");
    };
    let ExprKind::Call {
        dict_args,
        pending_dict_args,
        resolved_callee,
        ..
    } = &expr.kind
    else {
        panic!("third statement should be a call");
    };

    assert!(pending_dict_args.is_empty());
    assert!(dict_args.is_empty());
    match resolved_callee {
        Some(ResolvedCallee::DictMethod {
            dict: DictRef::Concrete(name),
            method,
        }) => {
            assert_eq!(name, "__Show__float");
            assert_eq!(method, "show");
        }
        other => panic!("expected concrete checked dict method, got {other:?}"),
    }
}

#[test]
fn legacy_qualified_trait_method_dot_syntax_is_not_trait_dispatch() {
    let err = infer_source_error(
        "trait Show 'a {
           fn show(x: 'a) -> string
         }

         impl Show for float {
           fn show(x) { \"ok\" }
         }

         Show.show(1.0)\n",
    );

    assert!(matches!(err.error.as_ref(), TypeError::UnboundVariable(name) if name == "Show"));
}

#[test]
fn qualified_trait_method_colon_colon_syntax_dispatches_trait_method() {
    let mut program = parse_source(
        "trait Show 'a {
           fn show(x: 'a) -> string
         }

         impl Show for float {
           fn show(x) { \"ok\" }
         }

         Show::show(1.0)\n",
    )
    .expect("source should parse");
    reassociate_standalone(&mut program).expect("source should reassociate");

    Infer::new()
        .infer_program(&mut program)
        .expect("qualified trait method should infer");
}

#[test]
fn reused_infer_does_not_leak_program_trait_operator_or_impl_state() {
    let mut first = parse_source(
        "trait Eq 'a {
           fn eq(lhs: 'a, rhs: 'a) -> bool
           fn infix 4 ==(lhs: 'a, rhs: 'a) -> bool
         }

         impl Eq for int {
           fn eq(lhs, rhs) { true }
           fn ==(lhs, rhs) { true }
         }

         1 == 1\n",
    )
    .expect("source should parse");
    reassociate_standalone(&mut first).expect("source should reassociate");

    let mut infer = Infer::new();
    infer
        .infer_program(&mut first)
        .expect("first program should infer");

    let mut no_trait = parse_source("Eq::eq(1, 1)\n").expect("source should parse");
    reassociate_standalone(&mut no_trait).expect("source should reassociate");
    let err = infer
        .infer_program(&mut no_trait)
        .expect_err("trait from first program should not leak");
    assert!(
        matches!(err.error.as_ref(), TypeError::InvalidInherentImplTarget(name) if name == "Eq"),
        "unexpected error: {err:?}"
    );

    let mut no_operator = parse_source("1 == 1\n").expect("source should parse");
    reassociate_standalone(&mut no_operator).expect("source should reassociate");
    let err = infer
        .infer_program(&mut no_operator)
        .expect_err("operator from first program should not leak");
    assert!(matches!(err.error.as_ref(), TypeError::UnboundVariable(name) if name == "=="));

    let mut no_impl = parse_source(
        "trait Eq 'a {
           fn eq(lhs: 'a, rhs: 'a) -> bool
         }

         Eq::eq(1, 1)\n",
    )
    .expect("source should parse");
    reassociate_standalone(&mut no_impl).expect("source should reassociate");
    let err = infer
        .infer_program(&mut no_impl)
        .expect_err("impl dictionary from first program should not leak");
    assert!(matches!(
        err.error.as_ref(),
        TypeError::MissingTraitImpl {
            trait_name,
            impl_target,
        } if trait_name == "Eq" && impl_target == "int"
    ));
}

#[test]
fn failed_impl_does_not_make_trait_unavailable_for_recovery() {
    let mut program = parse_source(
        "trait Show 'a {
           fn show(x: 'a) -> string
         }

         impl Show for int {
           fn show(x) { 1 }
         }

         Show::show(1)\n",
    )
    .expect("source should parse");
    reassociate_standalone(&mut program).expect("source should reassociate");

    let (_, diagnostics) = Infer::new().infer_program_collecting(&mut program, &[], None);

    assert_eq!(diagnostics.len(), 2);
    assert!(matches!(
        diagnostics[0].error.as_ref(),
        TypeError::Mismatch {
            expected: Ty::Con(expected),
            got: Ty::Int,
        } if expected == "string"
    ));
    assert!(matches!(
        diagnostics[1].error.as_ref(),
        TypeError::MissingTraitImpl {
            trait_name,
            impl_target,
        } if trait_name == "Show" && impl_target == "int"
    ));
}

fn infer_source_error(source: &str) -> SpannedTypeError {
    let mut program = parse_source(source).expect("source should parse");
    reassociate_standalone(&mut program).expect("source should reassociate");

    Infer::new()
        .infer_program(&mut program)
        .expect_err("source should fail inference")
}

#[test]
fn duplicate_record_fields_in_annotations_are_rejected() {
    let err = infer_source_error("let value: #{ x: int, x: float } = #{ x: 1 };\n");

    assert!(matches!(
        err.error.as_ref(),
        TypeError::DuplicateRecordField(field) if field == "x"
    ));
    assert_eq!(err.to_string(), "duplicate record field `x`");
}

#[test]
fn duplicate_record_fields_in_literals_are_rejected() {
    let err = infer_source_error("let value = #{ x: 1, x: 2 };\n");

    assert!(matches!(
        err.error.as_ref(),
        TypeError::DuplicateRecordField(field) if field == "x"
    ));
    assert_eq!(err.to_string(), "duplicate record field `x`");
}

#[test]
fn record_spread_field_collisions_are_rejected() {
    let err = infer_source_error("let base = #{ x: 1 };\nlet value = #{ ..base, x: 2 };\n");

    assert!(matches!(
        err.error.as_ref(),
        TypeError::DuplicateRecordField(field) if field == "x"
    ));
}

#[test]
fn bad_aggregate_entries_report_offending_span() {
    let bad_array_element = infer_source_error("let xs: [int] = [1, \"x\"];\n");
    assert_eq!(
        bad_array_element
            .span
            .expect("array element span")
            .start_col,
        21
    );

    let bad_array_spread = infer_source_error("let xs: [int] = [..1];\n");
    assert_eq!(
        bad_array_spread.span.expect("array spread span").start_col,
        20
    );

    let bad_record_spread = infer_source_error("let value = #{ ..1 };\n");
    assert_eq!(
        bad_record_spread
            .span
            .expect("record spread span")
            .start_col,
        18
    );
}

#[test]
fn unknown_constructor_pattern_reports_variant_context() {
    let source = "type Color = Red | Blue\nfn name(c: Color) -> string { match c { Purple -> \"purple\", _ -> \"other\" } }\n";
    let err = infer_source_error(source);

    assert!(matches!(
        err.error.as_ref(),
        TypeError::UnknownVariant { type_name, variant }
            if type_name == "Color" && variant == "Purple"
    ));
    let span = err.span.expect("unknown variant should have a span");
    assert_eq!(span.start_line, 2);
    assert_eq!(err.to_string(), "type `Color` has no variant `Purple`");
}

#[test]
fn unknown_constructor_pattern_on_unresolved_scrutinee_reports_nominal_context() {
    let err = infer_source_error("fn f(x) { match x { Missing -> 1 } }\n");

    assert!(matches!(
        err.error.as_ref(),
        TypeError::UnknownPatternConstructor {
            constructor,
            scrutinee
        } if constructor == "Missing" && matches!(scrutinee, Ty::Var(_))
    ));
    assert!(
        err.to_string().contains("expected a nominal type"),
        "unexpected diagnostic: {err}"
    );
}
