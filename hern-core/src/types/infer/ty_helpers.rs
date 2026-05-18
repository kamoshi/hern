//! Shared type-system helper predicates.
//!
//! This module holds cross-cutting helpers that do not yet warrant a narrower
//! home: callable capability extraction, function shape inspection, and small
//! fundep/constraint predicates used by trait dispatch.

use super::*;

pub(super) fn is_never(ty: &Ty) -> bool {
    matches!(ty, Ty::Never)
}

pub(super) fn range_ty(name: &str) -> Ty {
    Ty::App(Box::new(Ty::Con(name.to_string())), vec![Ty::Int])
}

pub(super) fn array_ty(element: Ty) -> Ty {
    Ty::App(Box::new(Ty::Con("Array".to_string())), vec![element])
}

pub(super) fn merge_record_field(
    fields: &mut Vec<(String, Ty)>,
    name: String,
    ty: Ty,
) -> Result<(), TypeError> {
    if fields.iter().any(|(existing, _)| existing == &name) {
        Err(TypeError::DuplicateRecordField(name))
    } else {
        fields.push((name, ty));
        Ok(())
    }
}

pub(super) fn merge_record_spread_tail(
    subst: &mut Subst,
    existing: Ty,
    next: Ty,
) -> Result<Ty, TypeError> {
    let existing = subst.apply(&existing);
    let next = subst.apply(&next);
    match (existing, next) {
        (Ty::Unit, tail) | (tail, Ty::Unit) => Ok(tail),
        (Ty::Var(left), Ty::Var(right)) if left == right => Ok(Ty::Var(left)),
        (left, right) => {
            unify(subst, left.clone(), right)?;
            Ok(subst.apply(&left))
        }
    }
}

pub(super) fn array_element_ty(ty: &Ty) -> Option<Ty> {
    match ty {
        Ty::App(con, args)
            if matches!(con.as_ref(), Ty::Con(name) if name == "Array") && args.len() == 1 =>
        {
            Some(args[0].clone())
        }
        _ => None,
    }
}

pub(super) fn func_param_capabilities(params: &[FuncParam]) -> Vec<ParamCapability> {
    params.iter().map(|param| param.capability).collect()
}

pub(super) fn func_return_capability(ty: &Ty) -> ReturnCapability {
    match ty {
        Ty::Func(_, ret) => ret.capability,
        _ => ReturnCapability::Value,
    }
}

pub(super) fn scheme_param_capabilities(scheme: &Scheme) -> Vec<ParamCapability> {
    match &scheme.ty {
        Ty::Func(params, _) => func_param_capabilities(params),
        _ => Vec::new(),
    }
}

pub(super) fn scheme_param_capability(scheme: &Scheme, idx: usize) -> ParamCapability {
    scheme_param_capabilities(scheme)
        .get(idx)
        .copied()
        .unwrap_or(ParamCapability::Value)
}

pub(super) fn expected_func_params(callee_ty: &Ty, arg_tys: Vec<Ty>) -> Vec<FuncParam> {
    match callee_ty {
        Ty::Func(params, _) if params.len() == arg_tys.len() => params
            .iter()
            .zip(arg_tys)
            .map(|(param, ty)| FuncParam {
                ty,
                capability: param.capability,
            })
            .collect(),
        _ => value_func_params(arg_tys),
    }
}

pub(super) fn expected_func_return(callee_ty: &Ty, ret_ty: Ty) -> FuncReturn {
    match callee_ty {
        Ty::Func(_, ret) => FuncReturn {
            ty: Box::new(ret_ty),
            capability: ret.capability,
        },
        _ => value_func_return(ret_ty),
    }
}

pub(super) fn has_mut_place_func_params(ty: &Ty) -> bool {
    matches!(ty, Ty::Func(params, _) if params.iter().any(|param| param.capability.is_mut_place()))
}

pub(super) fn is_unknown_trait_method_error(err: &SpannedTypeError) -> bool {
    matches!(err.error.as_ref(), TypeError::UnknownTraitMethod { .. })
}

pub(super) fn pattern_unknown_constructor_error(name: &str, scrutinee_ty: &Ty) -> TypeError {
    if let Some(type_name) = nominal_type_name(scrutinee_ty) {
        TypeError::UnknownVariant {
            type_name,
            variant: name.to_string(),
        }
    } else {
        TypeError::UnknownPatternConstructor {
            constructor: name.to_string(),
            scrutinee: scrutinee_ty.clone(),
        }
    }
}

pub(super) fn nominal_type_name(ty: &Ty) -> Option<String> {
    match ty {
        Ty::Con(name) => Some(name.clone()),
        Ty::App(con, _) => nominal_type_name(con),
        Ty::Qualified(_, inner) => nominal_type_name(inner),
        _ => None,
    }
}

pub(super) fn primary_param_or_panic(trait_def: &TraitDef) -> &str {
    trait_def
        .primary_param()
        .expect("parser rejects zero-parameter traits")
}

pub(super) fn primary_trait_var(args: &[Ty], determinant_indexes: &[usize]) -> Option<TyVar> {
    // Pending dictionary parameters are named by the first unresolved determinant.
    // Other determinants remain in the full predicate and are checked again when
    // final-pass dictionary resolution has more substitution information.
    // If every determinant is concrete but a dependent is still unresolved, use
    // that dependent only as a stable pending-dictionary name; matching still
    // compares the concrete determinant arguments before applying the fundep.
    debug_assert!(determinant_indexes.iter().all(|index| *index < args.len()));
    determinant_indexes
        .iter()
        .filter_map(|index| args.get(*index))
        .find_map(first_ty_var)
        .or_else(|| args.iter().find_map(first_ty_var))
}

pub(super) fn fundep_constraint_example(trait_def: &TraitDef) -> String {
    let determinant_indexes = trait_dict_indexes(trait_def);
    debug_assert!(
        crate::types::determinant_indexes_are_prefix(&determinant_indexes),
        "fundep constraint examples assume source arrows split a prefix determinant list"
    );
    let mut parts = Vec::new();
    for (index, param) in trait_def.params.iter().enumerate() {
        if index > 0 && index == determinant_indexes.len() {
            parts.push("->".to_string());
        }
        parts.push(param.clone());
    }
    format!("{}: {}", parts.join(" "), trait_def.name)
}

pub(super) fn determinants_share_var(
    left: &[Ty],
    right: &[Ty],
    determinant_indexes: &[usize],
    subst: &Subst,
) -> bool {
    debug_assert!(determinant_indexes.iter().all(|index| *index < left.len()));
    debug_assert!(determinant_indexes.iter().all(|index| *index < right.len()));
    if determinant_indexes.iter().all(|index| {
        let left = left.get(*index).map(|arg| subst.apply(arg));
        let right = right.get(*index).map(|arg| subst.apply(arg));
        left.is_some() && left == right
    }) {
        return true;
    }

    let mut left_vars = HashSet::new();
    for index in determinant_indexes {
        if let Some(arg) = left.get(*index) {
            free_type_vars_into(&subst.apply(arg), &mut left_vars);
        }
    }
    determinant_indexes.iter().any(|index| {
        right.get(*index).is_some_and(|arg| {
            free_type_vars(&subst.apply(arg))
                .iter()
                .any(|var| left_vars.contains(var))
        })
    })
}

pub(super) fn constraint_mentions_any_var(
    constraint: &TraitConstraint,
    vars: &HashSet<TyVar>,
    subst: &Subst,
) -> bool {
    if vars.is_empty() {
        return false;
    }
    let mut constraint_vars = HashSet::new();
    free_type_vars_into(&subst.apply(&Ty::Var(constraint.var)), &mut constraint_vars);
    for arg in &constraint.args {
        free_type_vars_into(&subst.apply(arg), &mut constraint_vars);
    }
    constraint_vars.iter().any(|var| vars.contains(var))
}

pub(super) fn ensure_operator_trait_has_params(
    trait_def: &TraitDef,
) -> Result<(), SpannedTypeError> {
    if trait_def.params.is_empty() {
        return Err(TypeError::TraitArityMismatch {
            trait_name: trait_def.name.clone(),
            expected: 1,
            got: 0,
        }
        .into());
    }
    Ok(())
}

pub(super) fn operator_trait_target_var(
    trait_def: &TraitDef,
    trait_args: &[Ty],
) -> Result<TyVar, SpannedTypeError> {
    let Some(first_arg) = trait_args.first() else {
        return Err(TypeError::TraitArityMismatch {
            trait_name: trait_def.name.clone(),
            expected: 1,
            got: 0,
        }
        .into());
    };
    let Ty::Var(target_var) = first_arg else {
        return Err(TypeError::InvalidTraitConstraint {
            trait_name: trait_def.name.clone(),
            message: "operator trait target must be an inferred type variable".to_string(),
        }
        .into());
    };
    Ok(*target_var)
}

pub(super) fn first_ty_var(ty: &Ty) -> Option<TyVar> {
    match ty {
        Ty::Var(var) => Some(*var),
        Ty::Qualified(constraints, inner) => first_ty_var(inner).or_else(|| {
            constraints
                .iter()
                .flat_map(|constraint| constraint.args.iter())
                .find_map(first_ty_var)
        }),
        Ty::Tuple(items) => items.iter().find_map(first_ty_var),
        Ty::Func(params, ret) => params
            .iter()
            .find_map(|param| first_ty_var(&param.ty))
            .or_else(|| first_ty_var(&ret.ty)),
        // Prefer the constructor first so HKT-shaped targets like `'f('a)` dispatch on `'f`.
        Ty::App(con, args) => first_ty_var(con).or_else(|| args.iter().find_map(first_ty_var)),
        Ty::Record(row) => row
            .fields
            .iter()
            .find_map(|(_, ty)| first_ty_var(ty))
            .or_else(|| first_ty_var(&row.tail)),
        Ty::Int | Ty::Float | Ty::Unit | Ty::Never | Ty::Con(_) => None,
    }
}

pub(super) fn walk_ast_type(ty: &Type, visit: &mut impl FnMut(&Type) -> bool) -> bool {
    if !visit(ty) {
        return false;
    }
    match ty {
        Type::App(con, args) => {
            if !walk_ast_type(con, visit) {
                return false;
            }
            for arg in args {
                if !walk_ast_type(arg, visit) {
                    return false;
                }
            }
        }
        Type::Func(params, ret) => {
            for param in params {
                if !walk_ast_type(&param.ty, visit) {
                    return false;
                }
            }
            if !walk_ast_type(&ret.ty, visit) {
                return false;
            }
        }
        Type::Tuple(items) => {
            for item in items {
                if !walk_ast_type(item, visit) {
                    return false;
                }
            }
        }
        Type::Record(fields, _) => {
            for (_, field_ty) in fields {
                if !walk_ast_type(field_ty, visit) {
                    return false;
                }
            }
        }
        Type::Ident(_) | Type::Var(_) | Type::Unit | Type::Never | Type::Hole => {}
    }
    true
}

pub(super) fn any_ast_type(ty: &Type, mut predicate: impl FnMut(&Type) -> bool) -> bool {
    let mut found = false;
    walk_ast_type(ty, &mut |node| {
        found = predicate(node);
        !found
    });
    found
}

/// Returns true if the AST `Type` mentions `var_name` as a type variable.
/// Used to decide whether a trait method's first parameter contains the HKT
/// trait parameter (e.g. `'f` in `'f('a)`), which determines the dispatch
/// strategy in `resolve_trait_method_call`.
pub(super) fn type_contains_var(ty: &Type, var_name: &str) -> bool {
    any_ast_type(
        ty,
        |node| matches!(node, Type::Var(name) if name == var_name),
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn determinant_matching_accepts_equal_concrete_determinants() {
        let subst = Subst::new();
        assert!(determinants_share_var(
            &[Ty::Con("Map".to_string()), Ty::Var(1)],
            &[Ty::Con("Map".to_string()), Ty::Var(2)],
            &[0],
            &subst,
        ));
        assert!(!determinants_share_var(
            &[Ty::Con("Map".to_string()), Ty::Var(1)],
            &[Ty::Con("Array".to_string()), Ty::Var(2)],
            &[0],
            &subst,
        ));
    }
}
