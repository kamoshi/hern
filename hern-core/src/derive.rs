use crate::ast::*;
use std::collections::HashSet;

pub fn expand_derives(program: &mut Program) {
    expand_derives_recovering(program);
}

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
                DeriveTrait::Eq => Stmt::Impl(derive_eq(&input)),
                DeriveTrait::ToString => Stmt::Impl(derive_to_string(&input)),
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
        "Eq",
        type_param_bounds(input, "Eq"),
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
                let binding = variant.payload.as_ref().map(|_| "__value".to_string());
                let expr = if variant.payload.is_some() {
                    concat(
                        concat(
                            string_lit(format!("{}(", variant.name)),
                            to_string_call(ident("__value")),
                        ),
                        string_lit(")"),
                    )
                } else {
                    string_lit(&variant.name)
                };
                (variant_pat(variant, binding.as_deref()), expr)
            })
            .collect(),
    });

    impl_def(
        input,
        "ToString",
        type_param_bounds(input, "ToString"),
        vec![impl_method(
            "to_string",
            vec![param(self_name)],
            body,
            input.source_span,
        )],
    )
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
    input
        .type_params
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
    Pattern::Constructor {
        name: variant.name.clone(),
        binding: binding
            .map(|name| Pattern::Variable(name.to_string(), SourceSpan::synthetic()))
            .map(Box::new),
    }
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

fn to_string_call(value: Expr) -> Expr {
    Expr::synthetic(ExprKind::Call {
        callee: Box::new(Expr::synthetic(ExprKind::AssociatedAccess {
            target: Type::Ident("ToString".to_string()),
            target_span: SourceSpan::synthetic(),
            member: "to_string".to_string(),
            member_span: SourceSpan::synthetic(),
            resolution: None,
        })),
        args: vec![value],
        is_method_call: false,
        arg_wrappers: vec![],
        resolved_callee: None,
        pending_trait_method: None,
        dict_args: vec![],
        pending_dict_args: vec![],
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::pipeline::parse_source;

    #[test]
    fn expand_derives_inserts_impls_after_type() {
        let mut program = parse_source("#[derive(Eq, ToString)]\ntype Box('a) = Box('a)\n")
            .expect("source should parse");

        expand_derives(&mut program);

        assert_eq!(program.stmts.len(), 3);
        assert!(matches!(program.stmts[0], Stmt::Type(_)));
        let Stmt::Impl(eq_impl) = &program.stmts[1] else {
            panic!("expected generated Eq impl");
        };
        let Stmt::Impl(to_string_impl) = &program.stmts[2] else {
            panic!("expected generated ToString impl");
        };
        assert_eq!(eq_impl.trait_name, "Eq");
        assert_eq!(to_string_impl.trait_name, "ToString");
        assert!(eq_impl.generated_by.is_some());
        assert!(to_string_impl.generated_by.is_some());
    }

    #[test]
    fn expand_derives_is_idempotent() {
        let mut program = parse_source("#[derive(Eq, ToString)]\ntype Box('a) = Box('a)\n")
            .expect("source should parse");

        expand_derives(&mut program);
        expand_derives(&mut program);

        assert_eq!(program.stmts.len(), 3);
        assert!(matches!(program.stmts[0], Stmt::Type(_)));
        assert!(matches!(program.stmts[1], Stmt::Impl(_)));
        assert!(matches!(program.stmts[2], Stmt::Impl(_)));
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
}
