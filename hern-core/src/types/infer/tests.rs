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
        TypeError::ArityMismatch {
            expected: 0,
            got: 1
        }
    ));
    assert!(matches!(
        diagnostics[1].error.as_ref(),
        TypeError::Mismatch(Ty::Unit, Ty::Int)
    ));
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
        TypeError::RecursiveTypeAlias(_)
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
        TypeError::Mismatch(Ty::Con(expected), Ty::Int) if expected == "string"
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
fn unknown_constructor_pattern_reports_variant_context() {
    let err = infer_source_error(
        "type Color = Red | Blue\nfn name(c: Color) -> string { match c { Purple -> \"purple\", _ -> \"other\" } }\n",
    );

    assert!(matches!(
        err.error.as_ref(),
        TypeError::UnknownVariant { type_name, variant }
            if type_name == "Color" && variant == "Purple"
    ));
    assert_eq!(err.to_string(), "type `Color` has no variant `Purple`");
}
