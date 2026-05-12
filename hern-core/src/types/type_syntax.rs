use crate::ast::{Expr, ExprKind, InherentMethod, Param, Pattern, Stmt, Type};
use crate::types::{Ty, error::TypeError};
use std::collections::HashSet;

pub(super) fn subst_hkt_param(ty: &Type, param: &str, target: &Type) -> Type {
    match ty {
        Type::App(con, args) if matches!(con.as_ref(), Type::Var(v) if v == param) => {
            if args.len() == 1 {
                apply_hole(target, &subst_hkt_param(&args[0], param, target))
            } else {
                ty.clone()
            }
        }
        Type::Var(v) if v == param => target.clone(),
        Type::App(con, args) => Type::App(
            Box::new(subst_hkt_param(con, param, target)),
            args.iter()
                .map(|a| subst_hkt_param(a, param, target))
                .collect(),
        ),
        Type::Func(params, ret) => Type::Func(
            params
                .iter()
                .map(|p| crate::ast::TypeParam {
                    ty: subst_hkt_param(&p.ty, param, target),
                    mut_place: p.mut_place,
                })
                .collect(),
            crate::ast::TypeReturn {
                ty: Box::new(subst_hkt_param(&ret.ty, param, target)),
                mut_place: ret.mut_place,
            },
        ),
        Type::Tuple(tys) => Type::Tuple(
            tys.iter()
                .map(|t| subst_hkt_param(t, param, target))
                .collect(),
        ),
        Type::Record(fields, open) => Type::Record(
            fields
                .iter()
                .map(|(n, t)| (n.clone(), subst_hkt_param(t, param, target)))
                .collect(),
            *open,
        ),
        other => other.clone(),
    }
}

fn apply_hole(target: &Type, arg: &Type) -> Type {
    if type_has_hole(target) {
        substitute_hole(target, arg)
    } else {
        Type::App(Box::new(target.clone()), vec![arg.clone()])
    }
}

fn type_has_hole(ty: &Type) -> bool {
    match ty {
        Type::Hole => true,
        Type::App(con, args) => type_has_hole(con) || args.iter().any(type_has_hole),
        _ => false,
    }
}

fn substitute_hole(ty: &Type, arg: &Type) -> Type {
    match ty {
        Type::Hole => arg.clone(),
        Type::App(con, args) => Type::App(
            Box::new(substitute_hole(con, arg)),
            args.iter().map(|a| substitute_hole(a, arg)).collect(),
        ),
        other => other.clone(),
    }
}

pub fn trait_impl_dict_name(trait_name: &str, target_key: &str) -> String {
    format!("__{}__{}", trait_name, target_key)
}

pub fn trait_impl_target_key_from_ast(target: &Type) -> Result<String, TypeError> {
    match target {
        Type::Ident(name) => Ok(name.clone()),
        Type::App(con, args) => {
            if args
                .iter()
                .all(|arg| exact_impl_target_key_from_ast(arg).is_ok())
            {
                exact_impl_target_key_from_ast(target)
            } else if generic_trait_impl_args(args) {
                trait_impl_target_key_from_ast(con)
            } else {
                Err(TypeError::InvalidTraitImplTarget(type_name_for_error(
                    target,
                )))
            }
        }
        _ => Err(TypeError::InvalidTraitImplTarget(type_name_for_error(
            target,
        ))),
    }
}

fn generic_trait_impl_args(args: &[Type]) -> bool {
    let mut seen_vars = HashSet::new();
    let mut hole_count = 0;

    for arg in args {
        match arg {
            Type::Var(var) => {
                if !seen_vars.insert(var) {
                    return false;
                }
            }
            Type::Hole => hole_count += 1,
            _ => return false,
        }
    }

    !args.is_empty() && (hole_count == 1 || hole_count == 0 && seen_vars.len() == args.len())
}

pub(crate) fn exact_impl_target_key_from_ast(target: &Type) -> Result<String, TypeError> {
    match target {
        Type::Ident(name) => Ok(name.clone()),
        Type::App(con, args) => {
            let mut key = exact_impl_target_key_from_ast(con)?;
            key.push_str("__app");
            key.push_str(&args.len().to_string());
            for arg in args {
                key.push_str("__");
                key.push_str(&exact_impl_target_key_from_ast(arg)?);
            }
            Ok(key)
        }
        _ => Err(TypeError::InvalidTraitImplTarget(type_name_for_error(
            target,
        ))),
    }
}

pub(super) fn inherent_impl_dict_name(target_name: &str) -> String {
    format!("__impl__{}", target_name)
}

pub(crate) fn inherent_impl_target_key_from_ast(
    target: &Type,
    declared_types: &HashSet<String>,
) -> Result<String, TypeError> {
    match target {
        Type::Ident(name) if is_named_inherent_target(name, declared_types) => Ok(name.clone()),
        Type::App(con, args) => {
            let Type::Ident(name) = con.as_ref() else {
                return Err(TypeError::InvalidInherentImplTarget(type_name_for_error(
                    target,
                )));
            };
            if !is_named_inherent_target(name, declared_types) {
                return Err(TypeError::InvalidInherentImplTarget(type_name_for_error(
                    target,
                )));
            }
            if args.iter().all(|arg| matches!(arg, Type::Var(_))) {
                let mut seen = HashSet::new();
                if args.iter().any(|arg| {
                    let Type::Var(var) = arg else {
                        return false;
                    };
                    !seen.insert(var)
                }) {
                    return Err(TypeError::InvalidInherentImplTarget(type_name_for_error(
                        target,
                    )));
                }
                return Ok(name.clone());
            }
            exact_impl_target_key_from_ast(target)
                .map_err(|_| TypeError::InvalidInherentImplTarget(type_name_for_error(target)))
        }
        _ => Err(TypeError::InvalidInherentImplTarget(type_name_for_error(
            target,
        ))),
    }
}

pub(super) fn is_self_param(param: &Param) -> bool {
    matches!(&param.pat, Pattern::Variable(name, _) if name == "self")
}

pub(super) fn substitute_self_in_inherent_method(method: &mut InherentMethod, target: &Type) {
    for param in &mut method.params {
        if let Some(ty) = &mut param.ty {
            substitute_self_in_type(ty, target);
        }
    }
    if let Some(ret_type) = &mut method.ret_type {
        substitute_self_in_type(&mut ret_type.ty, target);
    }
    substitute_self_in_expr_types(&mut method.body, target);
}

fn substitute_self_in_type(ty: &mut Type, target: &Type) {
    match ty {
        Type::Ident(name) if name == "Self" => *ty = target.clone(),
        Type::App(con, args) => {
            substitute_self_in_type(con, target);
            for arg in args {
                substitute_self_in_type(arg, target);
            }
        }
        Type::Func(params, ret) => {
            for param in params {
                substitute_self_in_type(&mut param.ty, target);
            }
            substitute_self_in_type(&mut ret.ty, target);
        }
        Type::Tuple(items) => {
            for item in items {
                substitute_self_in_type(item, target);
            }
        }
        Type::Record(fields, _) => {
            for (_, field_ty) in fields {
                substitute_self_in_type(field_ty, target);
            }
        }
        Type::Ident(_) | Type::Var(_) | Type::Unit | Type::Never | Type::Hole => {}
    }
}

fn substitute_self_in_expr_types(expr: &mut Expr, target: &Type) {
    match &mut expr.kind {
        ExprKind::Number(_)
        | ExprKind::StringLit(_)
        | ExprKind::Bool(_)
        | ExprKind::Ident(_)
        | ExprKind::Import(_)
        | ExprKind::Unit
        | ExprKind::Break(None)
        | ExprKind::Continue
        | ExprKind::Return(None) => {}
        ExprKind::AssociatedAccess {
            target: access_target,
            ..
        } => substitute_self_in_type(access_target, target),
        ExprKind::Not(expr)
        | ExprKind::Loop(expr)
        | ExprKind::Break(Some(expr))
        | ExprKind::Return(Some(expr))
        | ExprKind::FieldAccess { expr, .. } => substitute_self_in_expr_types(expr, target),
        ExprKind::Assign { target: lhs, value }
        | ExprKind::Binary {
            lhs, rhs: value, ..
        } => {
            substitute_self_in_expr_types(lhs, target);
            substitute_self_in_expr_types(value, target);
        }
        ExprKind::Call { callee, args, .. } => {
            substitute_self_in_expr_types(callee, target);
            for arg in args {
                substitute_self_in_expr_types(arg, target);
            }
        }
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
        } => {
            substitute_self_in_expr_types(cond, target);
            substitute_self_in_expr_types(then_branch, target);
            substitute_self_in_expr_types(else_branch, target);
        }
        ExprKind::Match { scrutinee, arms } => {
            substitute_self_in_expr_types(scrutinee, target);
            for (_, body) in arms {
                substitute_self_in_expr_types(body, target);
            }
        }
        ExprKind::Block { stmts, final_expr } => {
            for stmt in stmts {
                substitute_self_in_stmt_types(stmt, target);
            }
            if let Some(expr) = final_expr {
                substitute_self_in_expr_types(expr, target);
            }
        }
        ExprKind::Tuple(items) => {
            for item in items {
                substitute_self_in_expr_types(item, target);
            }
        }
        ExprKind::Array(entries) => {
            for entry in entries {
                substitute_self_in_expr_types(entry.expr_mut(), target);
            }
        }
        ExprKind::Record(entries) => {
            for entry in entries {
                substitute_self_in_expr_types(entry.expr_mut(), target);
            }
        }
        ExprKind::Lambda { params, body, .. } => {
            for param in params {
                if let Some(ty) = &mut param.ty {
                    substitute_self_in_type(ty, target);
                }
            }
            substitute_self_in_expr_types(body, target);
        }
        ExprKind::For { iterable, body, .. } => {
            substitute_self_in_expr_types(iterable, target);
            substitute_self_in_expr_types(body, target);
        }
    }
}

fn substitute_self_in_stmt_types(stmt: &mut Stmt, target: &Type) {
    match stmt {
        Stmt::Let { ty, value, .. } => {
            if let Some(ty) = ty {
                substitute_self_in_type(ty, target);
            }
            substitute_self_in_expr_types(value, target);
        }
        Stmt::Fn {
            params,
            ret_type,
            body,
            ..
        }
        | Stmt::Op {
            params,
            ret_type,
            body,
            ..
        } => {
            for param in params {
                if let Some(ty) = &mut param.ty {
                    substitute_self_in_type(ty, target);
                }
            }
            if let Some(ret_type) = ret_type {
                substitute_self_in_type(&mut ret_type.ty, target);
            }
            substitute_self_in_expr_types(body, target);
        }
        Stmt::Expr(expr) => substitute_self_in_expr_types(expr, target),
        // Nested item declarations own their own type scope. In particular, a nested
        // impl's `Self` is not the outer inherent impl's `Self`.
        Stmt::Trait(_)
        | Stmt::Impl(_)
        | Stmt::InherentImpl(_)
        | Stmt::Type(_)
        | Stmt::TypeAlias { .. }
        | Stmt::Extern { .. } => {}
    }
}

fn is_named_inherent_target(name: &str, declared_types: &HashSet<String>) -> bool {
    matches!(name, "string" | "int" | "float" | "bool") || declared_types.contains(name)
}

fn type_name_for_error(target: &Type) -> String {
    match target {
        Type::Ident(name) | Type::Var(name) => name.clone(),
        Type::App(con, args) => {
            let args = args
                .iter()
                .map(type_name_for_error)
                .collect::<Vec<_>>()
                .join(", ");
            format!("{}({})", type_name_for_error(con), args)
        }
        Type::Func(..) => "fn(...)".to_string(),
        Type::Tuple(_) => "(...)".to_string(),
        Type::Record(..) => "#{...}".to_string(),
        Type::Unit => "()".to_string(),
        Type::Never => "!".to_string(),
        Type::Hole => "*".to_string(),
    }
}

pub(crate) fn exact_impl_target_key_from_ty(ty: &Ty) -> Option<String> {
    match ty {
        Ty::Int => Some("int".to_string()),
        Ty::Float => Some("float".to_string()),
        Ty::Unit => Some("Unit".to_string()),
        Ty::Never => None,
        Ty::Con(name) => Some(name.clone()),
        Ty::App(con, args) => {
            let mut key = exact_impl_target_key_from_ty(con)?;
            key.push_str("__app");
            key.push_str(&args.len().to_string());
            for arg in args {
                key.push_str("__");
                key.push_str(&exact_impl_target_key_from_ty(arg)?);
            }
            Some(key)
        }
        Ty::Qualified(_, inner) => exact_impl_target_key_from_ty(inner),
        Ty::Var(_) | Ty::Tuple(_) | Ty::Func(_, _) | Ty::Record(_) => None,
    }
}

pub fn trait_impl_target_keys_from_ty(ty: &Ty) -> Vec<String> {
    match ty {
        Ty::Qualified(_, inner) => trait_impl_target_keys_from_ty(inner),
        Ty::App(con, _) => {
            let mut keys = Vec::new();
            if let Some(exact) = exact_impl_target_key_from_ty(ty) {
                keys.push(exact);
            }
            if let Some(generic) = exact_impl_target_key_from_ty(con)
                && keys.first() != Some(&generic)
            {
                keys.push(generic);
            }
            keys
        }
        _ => exact_impl_target_key_from_ty(ty).into_iter().collect(),
    }
}

pub fn inherent_impl_target_keys_from_ty(ty: &Ty) -> Vec<String> {
    trait_impl_target_keys_from_ty(ty)
}

pub(super) fn record_field_ty(ty: &Ty, field: &str) -> Option<Ty> {
    if let Ty::Record(row) = ty {
        row.fields
            .iter()
            .find(|(name, _)| name == field)
            .map(|(_, ty)| ty.clone())
    } else {
        None
    }
}
