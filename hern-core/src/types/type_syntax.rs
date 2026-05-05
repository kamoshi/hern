use crate::ast::Type;
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
                .map(|p| subst_hkt_param(p, param, target))
                .collect(),
            Box::new(subst_hkt_param(ret, param, target)),
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

pub(super) fn impl_target_name(target: &Type) -> String {
    match target {
        Type::Ident(name) => name.clone(),
        Type::App(con, _) => impl_target_name(con),
        _ => "Unknown".to_string(),
    }
}

pub(super) fn inherent_impl_dict_name(target_name: &str) -> String {
    format!("__impl__{}", target_name)
}

pub(super) fn validate_inherent_impl_target(
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
            if !is_named_inherent_target(name, declared_types)
                || args.iter().any(|arg| !matches!(arg, Type::Var(_)))
            {
                return Err(TypeError::InvalidInherentImplTarget(type_name_for_error(
                    target,
                )));
            }
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
            Ok(name.clone())
        }
        _ => Err(TypeError::InvalidInherentImplTarget(type_name_for_error(
            target,
        ))),
    }
}

fn is_named_inherent_target(name: &str, declared_types: &HashSet<String>) -> bool {
    matches!(name, "string" | "f64" | "bool") || declared_types.contains(name)
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
        Type::Hole => "*".to_string(),
    }
}

/// Returns `Some(name)` for concrete types that can name a trait dictionary,
/// or `None` for type variables and other unresolved types.
pub(super) fn ty_target_name(ty: &Ty) -> Option<String> {
    match ty {
        Ty::F64 => Some("f64".to_string()),
        Ty::Con(name) => Some(name.clone()),
        Ty::App(con, _) => ty_target_name(con),
        _ => None,
    }
}

pub(super) fn concrete_dict_name(trait_name: &str, ty: &Ty) -> Option<String> {
    ty_target_name(ty).map(|name| format!("__{}__{}", trait_name, name))
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
