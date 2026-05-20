use crate::ast::*;
use std::collections::HashSet;

const TRAIT_EQ: &str = "Eq";
const TRAIT_ORD: &str = "Ord";
const TRAIT_DEFAULT: &str = "Default";
const TRAIT_TO_STRING: &str = "ToString";
const METHOD_COMPARE: &str = "compare";
const METHOD_DEFAULT: &str = "default";
const METHOD_TO_STRING: &str = "to_string";

/// Expands all derive attributes in-place.
///
/// Derive expansion is deliberately infallible: unsupported generated impls are
/// reported later by type inference at the originating derive span.
pub fn expand_derives(program: &mut Program) {
    expand_derives_recovering(program);
}

/// Recovery-friendly derive expansion.
///
/// This currently performs the same infallible lowering as [`expand_derives`].
/// The separate entry point lets parser/type-checking recovery call the same
/// pass without implying that expansion itself can emit diagnostics.
pub fn expand_derives_recovering(program: &mut Program) {
    let mut expanded = Vec::with_capacity(program.stmts.len());

    for mut stmt in program.stmts.drain(..) {
        let generated = match &mut stmt {
            Stmt::Type(type_def) => lower_type_derives(type_def),
            _ => Vec::new(),
        };
        expanded.push(stmt);
        expanded.extend(generated);
    }

    program.stmts = expanded;
}

struct DeriveInput<'a> {
    source_span: SourceSpan,
    type_name: &'a str,
    type_params: &'a [String],
    variants: &'a [Variant],
}

fn lower_type_derives(type_def: &mut TypeDef) -> Vec<Stmt> {
    if type_def.derives.is_empty() {
        return Vec::new();
    }
    let mut out = Vec::new();
    let derives = std::mem::take(&mut type_def.derives);
    for derive in &derives {
        let input = DeriveInput {
            source_span: derive.span,
            type_name: &type_def.name,
            type_params: &type_def.params,
            variants: &type_def.variants,
        };
        for trait_name in &derive.traits {
            out.push(match trait_name {
                DeriveTrait::Default => Stmt::Impl(derive_default(&input)),
                DeriveTrait::Eq => Stmt::Impl(derive_eq(&input)),
                DeriveTrait::Ord => Stmt::Impl(derive_ord(&input)),
                DeriveTrait::ToString => Stmt::Impl(derive_to_string(&input)),
                DeriveTrait::Custom(_) => continue,
            });
        }
    }
    out
}

fn derive_eq(input: &DeriveInput<'_>) -> ImplDef {
    let lhs = "lhs";
    let rhs = "rhs";
    let eq_body = derive_eq_body(input, lhs, rhs, EqPolarity::Equal);
    let ne_body = derive_eq_body(input, lhs, rhs, EqPolarity::NotEqual);

    impl_def(
        input,
        TRAIT_EQ,
        type_param_bounds(input, TRAIT_EQ),
        vec![
            impl_method(
                "==",
                vec![param(lhs), param(rhs)],
                eq_body,
                input.source_span,
            ),
            impl_method(
                "!=",
                vec![param(lhs), param(rhs)],
                ne_body,
                input.source_span,
            ),
        ],
    )
}

#[derive(Clone, Copy)]
enum EqPolarity {
    Equal,
    NotEqual,
}

impl EqPolarity {
    fn payload_op(self) -> &'static str {
        match self {
            Self::Equal => "==",
            Self::NotEqual => "!=",
        }
    }

    fn same_empty_variant(self) -> bool {
        matches!(self, Self::Equal)
    }

    fn different_variant(self) -> bool {
        matches!(self, Self::NotEqual)
    }
}

fn derive_eq_body(input: &DeriveInput<'_>, lhs: &str, rhs: &str, polarity: EqPolarity) -> Expr {
    Expr::synthetic(ExprKind::Match {
        scrutinee: Box::new(ident(lhs)),
        arms: input
            .variants
            .iter()
            .map(|variant| {
                let lhs_binding = variant.payload.as_ref().map(|_| "__l0".to_string());
                let rhs_binding = variant.payload.as_ref().map(|_| "__r0".to_string());
                let rhs_same = if variant.payload.is_some() {
                    binary(ident("__l0"), polarity.payload_op(), ident("__r0"))
                } else {
                    bool_lit(polarity.same_empty_variant())
                };
                (
                    variant_pat(variant, lhs_binding.as_deref()),
                    Expr::synthetic(ExprKind::Match {
                        scrutinee: Box::new(ident(rhs)),
                        arms: vec![
                            (variant_pat(variant, rhs_binding.as_deref()), rhs_same),
                            (Pattern::Wildcard, bool_lit(polarity.different_variant())),
                        ],
                    }),
                )
            })
            .collect(),
    })
}

fn derive_to_string(input: &DeriveInput<'_>) -> ImplDef {
    let self_name = "self";
    let body = Expr::synthetic(ExprKind::Match {
        scrutinee: Box::new(ident(self_name)),
        arms: input
            .variants
            .iter()
            .map(|variant| {
                let payload = to_string_payload(variant.payload.as_ref());
                let expr = if let Some(payload) = &payload {
                    concat(
                        concat(
                            string_lit(format!("{}(", variant.name)),
                            payload.expr.clone(),
                        ),
                        string_lit(")"),
                    )
                } else {
                    string_lit(&variant.name)
                };
                (
                    variant_pat_with_payload(variant, payload.map(|payload| payload.pattern)),
                    expr,
                )
            })
            .collect(),
    });

    impl_def(
        input,
        TRAIT_TO_STRING,
        type_param_bounds(input, TRAIT_TO_STRING),
        vec![impl_method(
            METHOD_TO_STRING,
            vec![param(self_name)],
            body,
            input.source_span,
        )],
    )
}

#[derive(Clone)]
struct ToStringPayload {
    pattern: Pattern,
    expr: Expr,
}

fn to_string_payload(payload: Option<&Type>) -> Option<ToStringPayload> {
    match payload {
        Some(Type::Tuple(items)) => {
            let names = tuple_payload_names("__value", items.len());
            Some(ToStringPayload {
                pattern: tuple_payload_pattern(&names),
                expr: concat_to_string_fields(&names),
            })
        }
        Some(_) => Some(ToStringPayload {
            pattern: var_pat("__value"),
            expr: to_string_call(ident("__value")),
        }),
        None => None,
    }
}

fn concat_to_string_fields(names: &[String]) -> Expr {
    debug_assert!(
        !names.is_empty(),
        "tuple payload ToString generation expects at least one field"
    );
    let mut parts = Vec::new();
    for (index, name) in names.iter().enumerate() {
        if index > 0 {
            parts.push(string_lit(", "));
        }
        parts.push(to_string_call(ident(name)));
    }
    concat_exprs(parts)
        .expect("tuple payload ToString generation should have at least one expression")
}

fn concat_exprs(parts: Vec<Expr>) -> Option<Expr> {
    parts.into_iter().reduce(concat)
}

fn derive_default(input: &DeriveInput<'_>) -> ImplDef {
    let variant = default_variant(input);
    let type_bounds = variant
        .payload
        .as_ref()
        .map(|payload| type_param_bounds_for_type(payload, input.type_params, TRAIT_DEFAULT))
        .unwrap_or_default();
    impl_def(
        input,
        TRAIT_DEFAULT,
        type_bounds,
        vec![impl_method(
            METHOD_DEFAULT,
            vec![],
            default_value_for_variant(variant),
            input.source_span,
        )],
    )
}

fn default_variant<'a>(input: &'a DeriveInput<'_>) -> &'a Variant {
    if let Some(variant) = input
        .variants
        .iter()
        .find(|variant| variant.attrs.iter().any(|attr| attr.is("default")))
    {
        return variant;
    }
    if let Some(variant) = input
        .variants
        .iter()
        .find(|variant| variant.payload.is_none())
    {
        return variant;
    }
    input
        .variants
        .first()
        .expect("derive input should contain at least one variant")
}

fn default_value_for_variant(variant: &Variant) -> Expr {
    let Some(payload) = &variant.payload else {
        return ident(&variant.name);
    };

    // Hern variants currently have one payload slot. If that slot is a tuple,
    // synthesize a tuple of element defaults rather than requiring Default for
    // the tuple as a whole.
    let payload_default = match payload {
        Type::Tuple(items) => tuple(items.iter().map(|_| default_call()).collect()),
        _ => default_call(),
    };
    call(ident(&variant.name), vec![payload_default])
}

fn tuple(items: Vec<Expr>) -> Expr {
    Expr::synthetic(ExprKind::Tuple(items))
}

fn derive_ord(input: &DeriveInput<'_>) -> ImplDef {
    let lhs = "lhs";
    let rhs = "rhs";
    impl_def(
        input,
        TRAIT_ORD,
        type_param_bounds(input, TRAIT_ORD),
        vec![
            impl_method(
                "<",
                vec![param(lhs), param(rhs)],
                compare_result_eq(compare_call(ident(lhs), ident(rhs)), "LT"),
                input.source_span,
            ),
            impl_method(
                ">",
                vec![param(lhs), param(rhs)],
                compare_result_eq(compare_call(ident(lhs), ident(rhs)), "GT"),
                input.source_span,
            ),
            impl_method(
                "<=",
                vec![param(lhs), param(rhs)],
                compare_result_ne(compare_call(ident(lhs), ident(rhs)), "GT"),
                input.source_span,
            ),
            impl_method(
                ">=",
                vec![param(lhs), param(rhs)],
                compare_result_ne(compare_call(ident(lhs), ident(rhs)), "LT"),
                input.source_span,
            ),
            impl_method(
                METHOD_COMPARE,
                vec![param(lhs), param(rhs)],
                derive_ord_compare_body(input, lhs, rhs),
                input.source_span,
            ),
        ],
    )
}

fn derive_ord_compare_body(input: &DeriveInput<'_>, lhs: &str, rhs: &str) -> Expr {
    // This emits an explicit nested match: simple and direct, with O(n^2)
    // generated arms for n variants. If large enums become common, switch to a
    // tag comparison plus same-variant payload comparison.
    Expr::synthetic(ExprKind::Match {
        scrutinee: Box::new(ident(lhs)),
        arms: input
            .variants
            .iter()
            .enumerate()
            .map(|(lhs_index, lhs_variant)| {
                let ord_payload = ord_payload_compare(lhs_variant.payload.as_ref());
                (
                    variant_pat_with_payload(lhs_variant, ord_payload.lhs_pattern),
                    Expr::synthetic(ExprKind::Match {
                        scrutinee: Box::new(ident(rhs)),
                        arms: input
                            .variants
                            .iter()
                            .enumerate()
                            .map(|(rhs_index, rhs_variant)| {
                                let result = match lhs_index.cmp(&rhs_index) {
                                    std::cmp::Ordering::Less => ident("LT"),
                                    std::cmp::Ordering::Greater => ident("GT"),
                                    std::cmp::Ordering::Equal => ord_payload.compare.clone(),
                                };
                                let rhs_payload = if lhs_index == rhs_index {
                                    ord_payload.rhs_pattern.clone()
                                } else {
                                    wildcard_payload(rhs_variant.payload.as_ref())
                                };
                                (variant_pat_with_payload(rhs_variant, rhs_payload), result)
                            })
                            .collect(),
                    }),
                )
            })
            .collect(),
    })
}

#[derive(Clone)]
struct OrdPayloadCompare {
    lhs_pattern: Option<Pattern>,
    rhs_pattern: Option<Pattern>,
    compare: Expr,
}

fn ord_payload_compare(payload: Option<&Type>) -> OrdPayloadCompare {
    match payload {
        Some(Type::Tuple(items)) => {
            let lhs_names = tuple_payload_names("__l", items.len());
            let rhs_names = tuple_payload_names("__r", items.len());
            OrdPayloadCompare {
                lhs_pattern: Some(tuple_payload_pattern(&lhs_names)),
                rhs_pattern: Some(tuple_payload_pattern(&rhs_names)),
                compare: compare_tuple_payload_fields(&lhs_names, &rhs_names, 0),
            }
        }
        Some(_) => OrdPayloadCompare {
            lhs_pattern: Some(var_pat("__l0")),
            rhs_pattern: Some(var_pat("__r0")),
            compare: compare_call(ident("__l0"), ident("__r0")),
        },
        None => OrdPayloadCompare {
            lhs_pattern: None,
            rhs_pattern: None,
            compare: ident("EQ"),
        },
    }
}

fn tuple_payload_names(prefix: &str, len: usize) -> Vec<String> {
    (0..len).map(|index| format!("{prefix}{index}")).collect()
}

fn tuple_payload_pattern(names: &[String]) -> Pattern {
    Pattern::Tuple(names.iter().map(|name| var_pat(name)).collect())
}

fn compare_tuple_payload_fields(lhs_names: &[String], rhs_names: &[String], index: usize) -> Expr {
    if index >= lhs_names.len() {
        return ident("EQ");
    }
    Expr::synthetic(ExprKind::Match {
        scrutinee: Box::new(compare_call(
            ident(&lhs_names[index]),
            ident(&rhs_names[index]),
        )),
        arms: vec![
            (constructor_pat("LT"), ident("LT")),
            (constructor_pat("GT"), ident("GT")),
            (
                constructor_pat("EQ"),
                compare_tuple_payload_fields(lhs_names, rhs_names, index + 1),
            ),
        ],
    })
}

fn wildcard_payload(payload: Option<&Type>) -> Option<Pattern> {
    payload.map(|_| Pattern::Wildcard)
}

fn impl_def(
    input: &DeriveInput<'_>,
    trait_name: &str,
    type_bounds: Vec<TypeBound>,
    methods: Vec<ImplMethod>,
) -> ImplDef {
    let target = impl_target(input);
    #[allow(deprecated)]
    ImplDef {
        span: input.source_span,
        trait_name: trait_name.to_string(),
        target: target.clone(),
        trait_args: vec![target],
        dict_arg_indexes: vec![],
        used_fundep_arrow: false,
        fundep_arrow_index: None,
        type_bounds,
        dict_params: vec![],
        methods,
        generated_by: Some(GeneratedBy::Derive {
            trait_name: trait_name.to_string(),
            source_span: input.source_span,
        }),
    }
}

fn impl_target(input: &DeriveInput<'_>) -> Type {
    let con = Type::Ident(input.type_name.to_string());
    if input.type_params.is_empty() {
        con
    } else {
        Type::App(
            Box::new(con),
            input.type_params.iter().cloned().map(Type::Var).collect(),
        )
    }
}

fn type_param_bounds(input: &DeriveInput<'_>, trait_name: &str) -> Vec<TypeBound> {
    let mut used = HashSet::new();
    for variant in input.variants {
        if let Some(payload) = &variant.payload {
            collect_used_type_params(payload, input.type_params, &mut used);
        }
    }
    type_param_bounds_from_used(input.type_params, trait_name, used)
}

fn type_param_bounds_for_type(ty: &Type, params: &[String], trait_name: &str) -> Vec<TypeBound> {
    let mut used = HashSet::new();
    collect_used_type_params(ty, params, &mut used);
    type_param_bounds_from_used(params, trait_name, used)
}

fn type_param_bounds_from_used(
    params: &[String],
    trait_name: &str,
    used: HashSet<String>,
) -> Vec<TypeBound> {
    params
        .iter()
        .filter(|param| used.contains(*param))
        .map(|param| TypeBound {
            args: vec![Type::Var(param.clone())],
            fundep_arrow_index: None,
            traits: vec![trait_name.to_string()],
        })
        .collect()
}

fn collect_used_type_params(ty: &Type, params: &[String], used: &mut HashSet<String>) {
    match ty {
        Type::Var(name) if params.iter().any(|param| param == name) => {
            used.insert(name.clone());
        }
        Type::App(con, args) => {
            collect_used_type_params(con, params, used);
            for arg in args {
                collect_used_type_params(arg, params, used);
            }
        }
        Type::Func(args, ret) => {
            for arg in args {
                collect_used_type_params(&arg.ty, params, used);
            }
            collect_used_type_params(&ret.ty, params, used);
        }
        Type::Tuple(items) => {
            for item in items {
                collect_used_type_params(item, params, used);
            }
        }
        Type::Record(fields, _) => {
            for (_, field_ty) in fields {
                collect_used_type_params(field_ty, params, used);
            }
        }
        Type::Ident(_) | Type::Var(_) | Type::Unit | Type::Never | Type::Hole => {}
    }
}

fn impl_method(name: &str, params: Vec<Param>, body: Expr, source_span: SourceSpan) -> ImplMethod {
    ImplMethod {
        span: source_span,
        name: name.to_string(),
        name_span: source_span,
        params,
        ret_type: None,
        body,
        inline: false,
    }
}

fn param(name: &str) -> Param {
    Param::new(
        Pattern::Variable(name.to_string(), SourceSpan::synthetic()),
        None,
    )
}

fn variant_pat(variant: &Variant, binding: Option<&str>) -> Pattern {
    variant_pat_with_payload(variant, binding.map(var_pat))
}

fn variant_pat_with_payload(variant: &Variant, binding: Option<Pattern>) -> Pattern {
    Pattern::Constructor {
        name: variant.name.clone(),
        binding: binding.map(Box::new),
    }
}

fn constructor_pat(name: &str) -> Pattern {
    Pattern::Constructor {
        name: name.to_string(),
        binding: None,
    }
}

fn var_pat(name: &str) -> Pattern {
    Pattern::Variable(name.to_string(), SourceSpan::synthetic())
}

fn ident(name: &str) -> Expr {
    Expr::synthetic(ExprKind::Ident(name.to_string()))
}

fn bool_lit(value: bool) -> Expr {
    Expr::synthetic(ExprKind::Bool(value))
}

fn string_lit(value: impl Into<String>) -> Expr {
    Expr::synthetic(ExprKind::StringLit(value.into()))
}

fn call(callee: Expr, args: Vec<Expr>) -> Expr {
    Expr::synthetic(ExprKind::Call {
        callee: Box::new(callee),
        args,
        is_method_call: false,
        arg_wrappers: vec![],
        resolved_callee: None,
        pending_trait_method: None,
        dict_args: vec![],
        pending_dict_args: vec![],
    })
}

fn binary(lhs: Expr, op: &str, rhs: Expr) -> Expr {
    Expr::synthetic(ExprKind::Binary {
        lhs: Box::new(lhs),
        op: BinOp::Custom(op.to_string()),
        op_span: SourceSpan::synthetic(),
        rhs: Box::new(rhs),
        resolved_op: None,
        pending_op: None,
        dict_args: vec![],
        pending_dict_args: vec![],
    })
}

fn concat(lhs: Expr, rhs: Expr) -> Expr {
    binary(lhs, "<>", rhs)
}

fn compare_result_eq(value: Expr, ordering: &str) -> Expr {
    binary(value, "==", ident(ordering))
}

fn compare_result_ne(value: Expr, ordering: &str) -> Expr {
    binary(value, "!=", ident(ordering))
}

fn compare_call(lhs: Expr, rhs: Expr) -> Expr {
    associated_call(TRAIT_ORD, METHOD_COMPARE, vec![lhs, rhs])
}

fn default_call() -> Expr {
    associated_call(TRAIT_DEFAULT, METHOD_DEFAULT, vec![])
}

fn to_string_call(value: Expr) -> Expr {
    associated_call(TRAIT_TO_STRING, METHOD_TO_STRING, vec![value])
}

fn associated_call(target: &str, member: &str, args: Vec<Expr>) -> Expr {
    call(
        Expr::synthetic(ExprKind::AssociatedAccess {
            target: Type::Ident(target.to_string()),
            target_span: SourceSpan::synthetic(),
            member: member.to_string(),
            member_span: SourceSpan::synthetic(),
            resolution: None,
        }),
        args,
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::pipeline::parse_source;
    use crate::pipeline::reassociate_standalone;
    use crate::types::error::{SpannedTypeError, TypeError};
    use crate::types::infer::Infer;

    #[test]
    fn expand_derives_inserts_impls_after_type() {
        let mut program =
            parse_source("#[derive(Default, Eq, Ord, ToString)]\ntype Box('a) = Box('a)\n")
                .expect("source should parse");

        expand_derives(&mut program);

        assert_eq!(program.stmts.len(), 5);
        assert!(matches!(program.stmts[0], Stmt::Type(_)));
        let Stmt::Impl(default_impl) = &program.stmts[1] else {
            panic!("expected generated Default impl");
        };
        let Stmt::Impl(eq_impl) = &program.stmts[2] else {
            panic!("expected generated Eq impl");
        };
        let Stmt::Impl(ord_impl) = &program.stmts[3] else {
            panic!("expected generated Ord impl");
        };
        let Stmt::Impl(to_string_impl) = &program.stmts[4] else {
            panic!("expected generated ToString impl");
        };
        assert_eq!(default_impl.trait_name, "Default");
        assert_eq!(eq_impl.trait_name, "Eq");
        assert_eq!(ord_impl.trait_name, "Ord");
        assert_eq!(to_string_impl.trait_name, "ToString");
        assert!(default_impl.generated_by.is_some());
        assert!(eq_impl.generated_by.is_some());
        assert!(ord_impl.generated_by.is_some());
        assert!(to_string_impl.generated_by.is_some());
    }

    #[test]
    fn expand_derives_is_idempotent() {
        let mut program =
            parse_source("#[derive(Default, Eq, Ord, ToString)]\ntype Box('a) = Box('a)\n")
                .expect("source should parse");

        expand_derives(&mut program);
        expand_derives(&mut program);

        assert_eq!(program.stmts.len(), 5);
        assert!(matches!(program.stmts[0], Stmt::Type(_)));
        assert!(matches!(program.stmts[1], Stmt::Impl(_)));
        assert!(matches!(program.stmts[2], Stmt::Impl(_)));
        assert!(matches!(program.stmts[3], Stmt::Impl(_)));
        assert!(matches!(program.stmts[4], Stmt::Impl(_)));
    }

    #[test]
    fn expand_derives_adds_bounds_only_for_used_type_params() {
        let mut program = parse_source("#[derive(Eq)]\ntype Phantom('a, 'b) = Phantom('a)\n")
            .expect("source should parse");

        expand_derives(&mut program);

        let Stmt::Impl(eq_impl) = &program.stmts[1] else {
            panic!("expected generated Eq impl");
        };
        assert_eq!(eq_impl.type_bounds.len(), 1);
        assert!(matches!(
            eq_impl.type_bounds[0].args.as_slice(),
            [Type::Var(name)] if name == "'a"
        ));
    }

    #[test]
    fn to_string_derive_for_tuple_payload_checks_elements() {
        let mut program = parse_source("#[derive(ToString)]\ntype Pair('a, 'b) = Pair(('a, 'b))\n")
            .expect("source should parse");
        expand_derives(&mut program);

        let Stmt::Impl(to_string_impl) = &program.stmts[1] else {
            panic!("expected generated ToString impl");
        };
        let ExprKind::Match { arms, .. } = &to_string_impl.methods[0].body.kind else {
            panic!("ToString body should match on self");
        };
        let (pattern, expr) = &arms[0];
        assert!(matches!(
            pattern,
            Pattern::Constructor {
                binding: Some(binding),
                ..
            } if matches!(binding.as_ref(), Pattern::Tuple(items) if items.len() == 2)
        ));
        assert_eq!(to_string_call_arg_names(expr), vec!["__value0", "__value1"]);
    }

    #[test]
    fn default_derive_uses_first_empty_variant_without_payload_bounds() {
        let mut program =
            parse_source("#[derive(Default)]\ntype MaybeBox('a) = Present('a) | Missing\n")
                .expect("source should parse");

        expand_derives(&mut program);

        let Stmt::Impl(default_impl) = &program.stmts[1] else {
            panic!("expected generated Default impl");
        };
        assert!(default_impl.type_bounds.is_empty());
    }

    #[test]
    fn default_derive_for_function_payload_reports_derive_span() {
        let err = derive_infer_error(
            "trait Default 'a {
               fn default() -> 'a
             }

             #[derive(Default)]
             type Box = Box(fn(int) -> int)\n",
        );

        assert!(
            matches!(
                err.error.as_ref(),
                TypeError::DerivedImplFailure {
                    trait_name,
                    error,
                } if trait_name == "Default"
                    && matches!(
                        error.as_ref(),
                        TypeError::UnresolvedTrait { context, trait_name }
                            if context == "method call" && trait_name == "Default"
                    )
            ),
            "unexpected error: {err:?}"
        );
        assert_eq!(err.span.expect("derive span").start_line, 5);
    }

    #[test]
    fn eq_derive_for_concrete_payload_reports_derive_span() {
        let err = derive_infer_error(
            "trait Eq 'a {
               fn infix 4 ==(lhs: 'a, rhs: 'a) -> bool
               fn infix 4 !=(lhs: 'a, rhs: 'a) -> bool
             }

             #[derive(Eq)]
             type Box = Box(float)\n",
        );

        assert!(
            matches!(
                err.error.as_ref(),
                TypeError::DerivedImplFailure {
                    trait_name,
                    error,
                } if trait_name == "Eq"
                    && matches!(
                        error.as_ref(),
                        TypeError::MissingTraitImpl { trait_name, impl_target }
                            if trait_name == "Eq" && impl_target == "float"
                    )
            ),
            "unexpected error: {err:?}"
        );
        assert_eq!(err.span.expect("derive span").start_line, 6);
    }

    fn derive_infer_error(source: &str) -> SpannedTypeError {
        let mut program = parse_source(source).expect("source should parse");
        expand_derives(&mut program);
        reassociate_standalone(&mut program).expect("source should reassociate");

        Infer::new()
            .infer_program(&mut program)
            .expect_err("derived impl should fail inference")
    }

    fn to_string_call_arg_names(expr: &Expr) -> Vec<&str> {
        let mut names = Vec::new();
        collect_to_string_call_arg_names(expr, &mut names);
        names
    }

    fn collect_to_string_call_arg_names<'a>(expr: &'a Expr, names: &mut Vec<&'a str>) {
        match &expr.kind {
            ExprKind::Call { callee, args, .. } => {
                if let ExprKind::AssociatedAccess { member, .. } = &callee.kind
                    && member == METHOD_TO_STRING
                    && let Some(Expr {
                        kind: ExprKind::Ident(name),
                        ..
                    }) = args.first()
                {
                    names.push(name);
                }
                collect_to_string_call_arg_names(callee, names);
                for arg in args {
                    collect_to_string_call_arg_names(arg, names);
                }
            }
            ExprKind::Binary { lhs, rhs, .. } => {
                collect_to_string_call_arg_names(lhs, names);
                collect_to_string_call_arg_names(rhs, names);
            }
            ExprKind::Match { scrutinee, arms } => {
                collect_to_string_call_arg_names(scrutinee, names);
                for (_, body) in arms {
                    collect_to_string_call_arg_names(body, names);
                }
            }
            _ => {}
        }
    }
}
