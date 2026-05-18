//! Dictionary resolution and final AST dictionary attachment.
//!
//! Trait constraints become concrete dictionary references where possible, or
//! remain pending when generic code must receive dictionaries from its caller.
//! This module owns that transition and the final dictionary-attachment pass.

use crate::ast::*;
use crate::types::{
    Scheme, Subst, TraitConstraint, Ty, TypeEnv,
    error::TypeError,
    free_type_vars, perf,
    type_syntax::{
        trait_impl_arg_key_candidates_from_ty, trait_impl_dict_name_from_keys,
        trait_impl_target_keys_from_ty,
    },
    unify,
};
use std::collections::{HashMap, HashSet};

pub(super) fn dict_param_name(constraint: &TraitConstraint) -> String {
    // Preserve the historical unary-style dictionary parameter name when the
    // full predicate carries no extra information beyond the primary variable.
    if constraint
        .args
        .iter()
        .all(|arg| matches!(arg, Ty::Var(var) if *var == constraint.var))
    {
        return format!("__dict_{}_{}", constraint.trait_name, constraint.var);
    }
    let args = constraint
        .args
        .iter()
        .map(dict_param_ty_fragment)
        .collect::<Vec<_>>()
        .join("_");
    format!(
        "__dict_{}_{}_{}",
        constraint.trait_name, constraint.var, args
    )
}

pub(super) fn dict_ref_concrete_name(dict: &DictRef) -> Option<&str> {
    match dict {
        DictRef::Concrete(name) => Some(name.as_str()),
        DictRef::Applied { dict, .. } => Some(dict.as_str()),
        DictRef::Param(_) | DictRef::Structural(_) => None,
    }
}

#[allow(clippy::too_many_arguments)]
pub(super) fn attach_dict_args(
    env: &TypeEnv,
    known_impl_dicts: &HashSet<String>,
    known_impl_schemes: &HashMap<String, Scheme>,
    dict_args: &mut Vec<DictRef>,
    pending_dict_args: &mut Vec<PendingDictArg>,
    pending_constraints: &mut Vec<TraitConstraint>,
    constraints: &[TraitConstraint],
    subst: &mut Subst,
) -> Result<(), TypeError> {
    for constraint in constraints {
        let resolved = subst.apply(&Ty::Var(constraint.var));
        if let Ty::Var(var) = resolved {
            pending_constraints.push(TraitConstraint {
                var,
                trait_name: constraint.trait_name.clone(),
                args: constraint.args.iter().map(|arg| subst.apply(arg)).collect(),
                determinant_indexes: constraint.determinant_indexes.clone(),
            });
            pending_dict_args.push(PendingDictArg {
                var,
                trait_name: constraint.trait_name.clone(),
                args: constraint.args.iter().map(|arg| subst.apply(arg)).collect(),
                determinant_indexes: constraint.determinant_indexes.clone(),
            });
        } else if let Some(dict_ref) = resolve_concrete_from_args_unifying(
            &constraint.trait_name,
            &constraint
                .args
                .iter()
                .map(|arg| subst.apply(arg))
                .collect::<Vec<_>>(),
            &constraint.determinant_indexes,
            env,
            known_impl_dicts,
            known_impl_schemes,
            subst,
        ) {
            dict_args.push(dict_ref);
        } else {
            return Err(TypeError::MissingTraitImpl {
                trait_name: constraint.trait_name.clone(),
                impl_target: format!("{}", resolved),
            });
        }
    }
    Ok(())
}

pub(super) fn has_trait_impl(
    env: &TypeEnv,
    known_impl_dicts: &HashSet<String>,
    trait_name: &str,
    target_key: &str,
) -> bool {
    let dict_name = trait_impl_dict_name_from_keys(trait_name, &[target_key.to_string()]);
    env.get(&dict_name).is_some() || known_impl_dicts.contains(&dict_name)
}

fn resolve_local_dict_name(
    pending: &PendingDictArg,
    constraints: &[TraitConstraint],
    subst: &Subst,
) -> Option<DictRef> {
    let resolved = subst.apply(&Ty::Var(pending.var));
    if matches!(resolved, Ty::Var(_)) {
        constraints
            .iter()
            .find(|constraint| local_constraint_matches_pending(constraint, pending, subst))
            .map(|constraint| DictRef::Param(dict_param_name(constraint)))
    } else {
        None
    }
}

fn local_constraint_matches_pending(
    constraint: &TraitConstraint,
    pending: &PendingDictArg,
    subst: &Subst,
) -> bool {
    // Local dictionary reuse must match the already-normalized predicate exactly.
    // Unifying here would mutate selection instead of merely finding the dict
    // parameter owned by the current callable.
    constraint.trait_name == pending.trait_name
        && constraint.determinant_indexes == pending.determinant_indexes
        && constraint.args.len() == pending.args.len()
        && constraint
            .args
            .iter()
            .zip(&pending.args)
            .all(|(constraint_arg, pending_arg)| {
                subst.apply(constraint_arg) == subst.apply(pending_arg)
            })
}

fn dict_param_ty_fragment(ty: &Ty) -> String {
    match ty {
        Ty::Int => "int".to_string(),
        Ty::Float => "float".to_string(),
        Ty::Unit => "unit".to_string(),
        Ty::Never => "never".to_string(),
        Ty::Var(var) => format!("v{var}"),
        Ty::Con(name) => format!("c{}", stable_name_fragment(name)),
        Ty::App(con, args) => format!(
            "app{}_{}",
            dict_param_ty_fragment(con),
            list_fragment(args.iter().map(dict_param_ty_fragment))
        ),
        Ty::Tuple(items) => format!(
            "tuple{}",
            list_fragment(items.iter().map(dict_param_ty_fragment))
        ),
        Ty::Func(params, ret) => {
            let params =
                list_fragment(params.iter().map(|param| dict_param_ty_fragment(&param.ty)));
            format!("fn{params}_ret{}", dict_param_ty_fragment(&ret.ty))
        }
        Ty::Record(row) => format!(
            "record{}_tail{}",
            list_fragment(row.fields.iter().map(|(name, ty)| format!(
                "{}_{}",
                stable_name_fragment(name),
                dict_param_ty_fragment(ty)
            ))),
            dict_param_ty_fragment(&row.tail)
        ),
        Ty::Qualified(constraints, inner) => format!(
            "qualified{}_inner{}",
            list_fragment(constraints.iter().map(|constraint| format!(
                "{}{}",
                stable_name_fragment(&constraint.trait_name),
                list_fragment(constraint.args.iter().map(dict_param_ty_fragment))
            ))),
            dict_param_ty_fragment(inner)
        ),
    }
}

fn stable_name_fragment(input: &str) -> String {
    let mut out = String::new();
    for byte in input.as_bytes() {
        if byte.is_ascii_alphanumeric() || *byte == b'_' {
            out.push(char::from(*byte));
        } else {
            out.push('x');
            out.push_str(&format!("{byte:02x}"));
        }
    }
    format!("{}_{out}", input.len())
}

fn list_fragment(items: impl Iterator<Item = String>) -> String {
    let items = items.collect::<Vec<_>>();
    format!(
        "{}_{}",
        items.len(),
        items
            .into_iter()
            .map(|item| format!("{}_{item}", item.len()))
            .collect::<Vec<_>>()
            .join("_")
    )
}

pub(super) fn resolve_local_or_concrete(
    pending: &PendingDictArg,
    constraints: &[TraitConstraint],
    env: &TypeEnv,
    known_impl_dicts: &HashSet<String>,
    known_impl_schemes: &HashMap<String, Scheme>,
    subst: &Subst,
) -> Option<DictRef> {
    resolve_local_dict_name(pending, constraints, subst)
        .or_else(|| resolve_concrete(pending, env, known_impl_dicts, known_impl_schemes, subst))
}

pub(super) fn resolve_concrete(
    pending: &PendingDictArg,
    env: &TypeEnv,
    known_impl_dicts: &HashSet<String>,
    known_impl_schemes: &HashMap<String, Scheme>,
    subst: &Subst,
) -> Option<DictRef> {
    let args = pending_args(pending, subst);
    resolve_concrete_from_args(
        &pending.trait_name,
        &args,
        &pending.determinant_indexes,
        env,
        known_impl_dicts,
        known_impl_schemes,
    )
}

fn pending_args(pending: &PendingDictArg, subst: &Subst) -> Vec<Ty> {
    assert!(
        !pending.args.is_empty(),
        "pending dictionary args must carry the full trait predicate"
    );
    pending.args.iter().map(|arg| subst.apply(arg)).collect()
}

fn resolve_concrete_from_args(
    trait_name: &str,
    args: &[Ty],
    determinant_indexes: &[usize],
    env: &TypeEnv,
    known_impl_dicts: &HashSet<String>,
    known_impl_schemes: &HashMap<String, Scheme>,
) -> Option<DictRef> {
    if args.len() == 1 {
        return resolve_concrete_dict_ref(
            trait_name,
            &args[0],
            env,
            known_impl_dicts,
            known_impl_schemes,
        );
    }
    resolve_concrete_multi_dict_ref(
        trait_name,
        args,
        determinant_indexes,
        env,
        known_impl_dicts,
        known_impl_schemes,
    )
}

pub(super) fn resolve_concrete_from_args_unifying(
    trait_name: &str,
    args: &[Ty],
    determinant_indexes: &[usize],
    env: &TypeEnv,
    known_impl_dicts: &HashSet<String>,
    known_impl_schemes: &HashMap<String, Scheme>,
    subst: &mut Subst,
) -> Option<DictRef> {
    if args.len() == 1 {
        return resolve_concrete_dict_ref(
            trait_name,
            &args[0],
            env,
            known_impl_dicts,
            known_impl_schemes,
        );
    }
    let mut candidate_sets = Vec::new();
    for index in determinant_indexes {
        let candidates = trait_impl_arg_key_candidates_from_ty(args.get(*index)?);
        if candidates.is_empty() {
            return resolve_concrete_from_impl_schemes_unifying(
                trait_name,
                args,
                env,
                known_impl_dicts,
                known_impl_schemes,
                subst,
            );
        }
        candidate_sets.push(candidates);
    }
    find_cartesian_key_match(&candidate_sets, |keys| {
        let dict_name = trait_impl_dict_name_from_keys(trait_name, keys);
        let scheme = env
            .get(&dict_name)
            .map(|info| info.scheme.clone())
            .or_else(|| known_impl_schemes.get(&dict_name).cloned());
        let Some(scheme) = scheme else {
            if known_impl_dicts.contains(&dict_name) {
                return Some(DictRef::Concrete(dict_name));
            }
            return None;
        };
        let mut trial = subst.clone();
        if !unify_scheme_method_actuals(&scheme.ty, args, &mut trial) {
            return None;
        }
        let resolved_args = args.iter().map(|arg| trial.apply(arg)).collect::<Vec<_>>();
        let dict_args = dict_ref_args_for_scheme_args(
            &scheme,
            &resolved_args,
            env,
            known_impl_dicts,
            known_impl_schemes,
        )?;
        *subst = trial;
        if dict_args.is_empty() {
            Some(DictRef::Concrete(dict_name))
        } else {
            Some(DictRef::Applied {
                dict: dict_name,
                args: dict_args,
            })
        }
    })
    .or_else(|| {
        resolve_concrete_from_impl_schemes_unifying(
            trait_name,
            args,
            env,
            known_impl_dicts,
            known_impl_schemes,
            subst,
        )
    })
}

fn resolve_concrete_from_impl_schemes_unifying(
    trait_name: &str,
    args: &[Ty],
    env: &TypeEnv,
    known_impl_dicts: &HashSet<String>,
    known_impl_schemes: &HashMap<String, Scheme>,
    subst: &mut Subst,
) -> Option<DictRef> {
    if !args
        .iter()
        .any(|arg| ty_has_concrete_shape(&subst.apply(arg)))
    {
        return None;
    }

    let mut candidates = impl_scheme_candidates(trait_name, env, known_impl_schemes);
    // Deterministic fallback for shape-based scheme lookup. Hern does not yet
    // report overlapping parameterized impls as ambiguity here, so sorted names
    // keep selection stable until a real ambiguity diagnostic exists.
    candidates.sort_by_key(|(dict_name, _)| *dict_name);

    for (dict_name, scheme) in candidates {
        let mut trial = subst.clone();
        if !unify_scheme_method_actuals(&scheme.ty, args, &mut trial) {
            continue;
        }
        let resolved_args = args.iter().map(|arg| trial.apply(arg)).collect::<Vec<_>>();
        let Some(dict_args) = dict_ref_args_for_scheme_args(
            scheme,
            &resolved_args,
            env,
            known_impl_dicts,
            known_impl_schemes,
        ) else {
            continue;
        };
        *subst = trial;
        return if dict_args.is_empty() {
            Some(DictRef::Concrete(dict_name.to_string()))
        } else {
            Some(DictRef::Applied {
                dict: dict_name.to_string(),
                args: dict_args,
            })
        };
    }

    None
}

fn impl_scheme_candidates<'a>(
    trait_name: &str,
    env: &'a TypeEnv,
    known_impl_schemes: &'a HashMap<String, Scheme>,
) -> Vec<(&'a str, &'a Scheme)> {
    let prefix = format!("__{trait_name}__");
    let mut candidates = Vec::new();
    let mut seen = HashSet::new();
    for (name, info) in env.iter() {
        if name.starts_with(&prefix) {
            seen.insert(name.as_str());
            candidates.push((name.as_str(), &info.scheme));
        }
    }
    for (name, scheme) in known_impl_schemes {
        if name.starts_with(&prefix) && seen.insert(name.as_str()) {
            candidates.push((name.as_str(), scheme));
        }
    }
    candidates
}

fn ty_has_concrete_shape(ty: &Ty) -> bool {
    match ty {
        Ty::Var(_) => false,
        Ty::Qualified(_, inner) => ty_has_concrete_shape(inner),
        Ty::Func(params, ret) => {
            params.iter().any(|param| ty_has_concrete_shape(&param.ty))
                || ty_has_concrete_shape(&ret.ty)
        }
        Ty::Tuple(items) => items.iter().any(ty_has_concrete_shape),
        Ty::App(con, args) => ty_has_concrete_shape(con) || args.iter().any(ty_has_concrete_shape),
        Ty::Record(row) => {
            row.fields.iter().any(|(_, ty)| ty_has_concrete_shape(ty))
                || ty_has_concrete_shape(&row.tail)
        }
        Ty::Int | Ty::Float | Ty::Unit | Ty::Never | Ty::Con(_) => true,
    }
}

pub(super) fn resolve_concrete_dict_ref(
    trait_name: &str,
    ty: &Ty,
    env: &TypeEnv,
    known_impl_dicts: &HashSet<String>,
    known_impl_schemes: &HashMap<String, Scheme>,
) -> Option<DictRef> {
    if trait_name == "Eq"
        && let Ty::Tuple(items) = ty
    {
        let args = items
            .iter()
            .map(|item| {
                resolve_concrete_dict_ref("Eq", item, env, known_impl_dicts, known_impl_schemes)
            })
            .collect::<Option<Vec<_>>>()?;
        return Some(DictRef::Structural(StructuralDictRef {
            trait_name: "Eq".to_string(),
            target: DictTarget::Tuple(items.len()),
            args,
        }));
    }
    for target_key in trait_impl_target_keys_from_ty(ty) {
        if has_trait_impl(env, known_impl_dicts, trait_name, &target_key) {
            let dict_name =
                trait_impl_dict_name_from_keys(trait_name, std::slice::from_ref(&target_key));
            let scheme = env
                .get(&dict_name)
                .map(|info| info.scheme.clone())
                .or_else(|| known_impl_schemes.get(&dict_name).cloned());
            let args = if let Some(scheme) = scheme.as_ref() {
                dict_ref_args_for_scheme(scheme, ty, env, known_impl_dicts, known_impl_schemes)?
            } else {
                Vec::new()
            };
            return if args.is_empty() {
                Some(DictRef::Concrete(dict_name))
            } else {
                Some(DictRef::Applied {
                    dict: dict_name,
                    args,
                })
            };
        }
    }
    None
}

pub(super) fn resolve_concrete_multi_dict_ref(
    trait_name: &str,
    args: &[Ty],
    determinant_indexes: &[usize],
    env: &TypeEnv,
    known_impl_dicts: &HashSet<String>,
    known_impl_schemes: &HashMap<String, Scheme>,
) -> Option<DictRef> {
    let mut candidate_sets = Vec::new();
    for index in determinant_indexes {
        let candidates = trait_impl_arg_key_candidates_from_ty(args.get(*index)?);
        if candidates.is_empty() {
            return None;
        }
        candidate_sets.push(candidates);
    }
    find_cartesian_key_match(&candidate_sets, |keys| {
        let dict_name = trait_impl_dict_name_from_keys(trait_name, keys);
        if env.get(&dict_name).is_none() && !known_impl_dicts.contains(&dict_name) {
            return None;
        }
        let scheme = env
            .get(&dict_name)
            .map(|info| info.scheme.clone())
            .or_else(|| known_impl_schemes.get(&dict_name).cloned());
        let dict_args = if let Some(scheme) = scheme.as_ref() {
            dict_ref_args_for_scheme_args(scheme, args, env, known_impl_dicts, known_impl_schemes)?
        } else {
            Vec::new()
        };
        if dict_args.is_empty() {
            Some(DictRef::Concrete(dict_name))
        } else {
            Some(DictRef::Applied {
                dict: dict_name,
                args: dict_args,
            })
        }
    })
}

fn find_cartesian_key_match<T>(
    candidate_sets: &[Vec<String>],
    mut f: impl FnMut(&[String]) -> Option<T>,
) -> Option<T> {
    perf::cartesian_search_call();
    fn search<T>(
        candidate_sets: &[Vec<String>],
        index: usize,
        current: &mut Vec<String>,
        f: &mut impl FnMut(&[String]) -> Option<T>,
    ) -> Option<T> {
        if index == candidate_sets.len() {
            perf::cartesian_search_leaf();
            return f(current);
        }
        for candidate in &candidate_sets[index] {
            current.push(candidate.clone());
            if let Some(found) = search(candidate_sets, index + 1, current, f) {
                return Some(found);
            }
            current.pop();
        }
        None
    }

    let mut current = Vec::with_capacity(candidate_sets.len());
    search(candidate_sets, 0, &mut current, &mut f)
}

fn dict_ref_args_for_scheme(
    scheme: &Scheme,
    target_ty: &Ty,
    env: &TypeEnv,
    known_impl_dicts: &HashSet<String>,
    known_impl_schemes: &HashMap<String, Scheme>,
) -> Option<Vec<DictRef>> {
    dict_ref_args_for_scheme_args(
        scheme,
        std::slice::from_ref(target_ty),
        env,
        known_impl_dicts,
        known_impl_schemes,
    )
}

fn dict_ref_args_for_scheme_args(
    scheme: &Scheme,
    actual_args: &[Ty],
    env: &TypeEnv,
    known_impl_dicts: &HashSet<String>,
    known_impl_schemes: &HashMap<String, Scheme>,
) -> Option<Vec<DictRef>> {
    if scheme.constraints.is_empty() {
        return Some(Vec::new());
    }
    let bindings = bind_scheme_target_vars(&scheme.ty, actual_args, &scheme.constraints)?;
    scheme
        .constraints
        .iter()
        .map(|constraint| {
            let ty = bindings.get(&constraint.var)?;
            // Dictionary arguments can only be materialized once their dispatch
            // type is concrete; unresolved arguments stay pending for a later pass.
            if ty_has_unresolved_var(ty) {
                return None;
            }
            resolve_concrete_dict_ref(
                &constraint.trait_name,
                ty,
                env,
                known_impl_dicts,
                known_impl_schemes,
            )
        })
        .collect()
}

fn bind_scheme_target_vars(
    dict_ty: &Ty,
    actual_args: &[Ty],
    constraints: &[TraitConstraint],
) -> Option<HashMap<u32, Ty>> {
    let Ty::Record(row) = dict_ty else {
        return None;
    };
    let mut bindings = HashMap::new();
    for (_, field_ty) in &row.fields {
        // A dictionary can have helper methods that each expose only part of a
        // constrained impl type. Accumulate compatible bindings across fields
        // until every constraint can be materialized.
        if let Ty::Func(params, _) = field_ty
            && bind_func_vars_to_actuals(field_ty, params, actual_args, &mut bindings)
            && constraints
                .iter()
                .all(|constraint| bindings.contains_key(&constraint.var))
        {
            return Some(bindings);
        }
    }
    None
}

fn unify_scheme_method_actuals(dict_ty: &Ty, actual_args: &[Ty], subst: &mut Subst) -> bool {
    let Ty::Record(row) = dict_ty else {
        return false;
    };
    for (_, field_ty) in &row.fields {
        let Ty::Func(params, ret) = field_ty else {
            continue;
        };
        if actual_args.is_empty() || params.len() > actual_args.len() {
            continue;
        }
        let mut trial = subst.clone();
        let params_ok = params
            .iter()
            .zip(actual_args)
            .all(|(param, actual)| unify(&mut trial, param.ty.clone(), actual.clone()).is_ok());
        if !params_ok {
            continue;
        }
        if let Some(actual_ret) = actual_args.get(params.len())
            && unify(&mut trial, *ret.ty.clone(), actual_ret.clone()).is_err()
        {
            continue;
        }
        *subst = trial;
        return true;
    }
    false
}

fn bind_func_vars_to_actuals(
    field_ty: &Ty,
    params: &[crate::types::FuncParam],
    actual_args: &[Ty],
    bindings: &mut HashMap<u32, Ty>,
) -> bool {
    if actual_args.is_empty() {
        return false;
    }
    // `actual_args` are trait arguments, not method-call arguments. A unary trait
    // such as `Eq` has one trait argument but two method parameters, so binding
    // from the shared prefix is the intended path for schemes like
    // `impl Eq for Box('a) where 'a: Eq`.
    let mut local = bindings.clone();
    for (param, actual) in params.iter().zip(actual_args) {
        if !bind_ty_vars_to_actual(&param.ty, actual, &mut local) {
            return false;
        }
    }
    if let Ty::Func(_, ret) = field_ty
        && let Some(actual_ret) = actual_args.get(params.len())
        && !bind_ty_vars_to_actual(&ret.ty, actual_ret, &mut local)
    {
        return false;
    }
    *bindings = local;
    true
}

fn bind_ty_vars_to_actual(pattern: &Ty, actual: &Ty, bindings: &mut HashMap<u32, Ty>) -> bool {
    match (pattern, actual) {
        (Ty::Var(var), actual) => {
            if let Some(existing) = bindings.get(var) {
                return existing == actual;
            }
            bindings.insert(*var, actual.clone());
            true
        }
        (Ty::App(p_con, p_args), Ty::App(a_con, a_args)) if p_args.len() == a_args.len() => {
            bind_ty_vars_to_actual(p_con, a_con, bindings)
                && p_args
                    .iter()
                    .zip(a_args)
                    .all(|(p, a)| bind_ty_vars_to_actual(p, a, bindings))
        }
        (Ty::Con(p), Ty::Con(a)) => p == a,
        (Ty::Int, Ty::Int) | (Ty::Float, Ty::Float) | (Ty::Unit, Ty::Unit) => true,
        (Ty::Qualified(_, p), a) => bind_ty_vars_to_actual(p, a, bindings),
        (p, Ty::Qualified(_, a)) => bind_ty_vars_to_actual(p, a, bindings),
        _ => false,
    }
}

fn ty_has_unresolved_var(ty: &Ty) -> bool {
    match ty {
        Ty::Var(_) => true,
        Ty::Qualified(_, inner) => ty_has_unresolved_var(inner),
        Ty::Func(params, ret) => {
            params.iter().any(|param| ty_has_unresolved_var(&param.ty))
                || ty_has_unresolved_var(&ret.ty)
        }
        Ty::Tuple(items) => items.iter().any(ty_has_unresolved_var),
        Ty::App(con, args) => ty_has_unresolved_var(con) || args.iter().any(ty_has_unresolved_var),
        Ty::Record(row) => {
            row.fields.iter().any(|(_, ty)| ty_has_unresolved_var(ty))
                || ty_has_unresolved_var(&row.tail)
        }
        Ty::Int | Ty::Float | Ty::Unit | Ty::Never | Ty::Con(_) => false,
    }
}

/// Resolve all `pending_dict_args` / `pending_op` / `pending_iter` nodes in an
/// expression tree.
///
/// `resolve` maps a pending arg to a dict name (or `None` if not yet concrete).
/// `process_fn` controls whether `Stmt::Fn` / `Stmt::Op` inside block
/// expressions are recursed into: `false` during the per-function local pass
/// (those bodies are resolved by their own call), `true` during the global
/// final pass.
pub(super) fn resolve_dict_uses_expr(
    expr: &mut Expr,
    resolve: &impl Fn(&PendingDictArg) -> Option<DictRef>,
    process_fn: bool,
) -> Result<(), TypeError> {
    resolve_dict_uses_expr_with_mode(expr, resolve, process_fn, DictResolveMode::HardUnresolved)
}

pub(super) fn resolve_dict_uses_expr_lenient(
    expr: &mut Expr,
    resolve: &impl Fn(&PendingDictArg) -> Option<DictRef>,
    process_fn: bool,
) -> Result<(), TypeError> {
    resolve_dict_uses_expr_with_mode(expr, resolve, process_fn, DictResolveMode::Lenient)
}

#[derive(Clone, Copy)]
enum DictResolveMode {
    HardUnresolved,
    Lenient,
}

impl DictResolveMode {
    fn is_hard(self) -> bool {
        matches!(self, Self::HardUnresolved)
    }
}

fn resolve_dict_uses_expr_with_mode(
    expr: &mut Expr,
    resolve: &impl Fn(&PendingDictArg) -> Option<DictRef>,
    process_fn: bool,
    mode: DictResolveMode,
) -> Result<(), TypeError> {
    match &mut expr.kind {
        ExprKind::Binary {
            lhs,
            rhs,
            op,
            resolved_op,
            pending_op,
            dict_args,
            pending_dict_args,
            ..
        } => {
            if let BinOp::Custom(op_str) = op
                && let Some(pending) = pending_op.as_ref()
            {
                if let Some(dict) = resolve(pending) {
                    *resolved_op = Some(ResolvedCallee::DictMethod {
                        dict,
                        method: op_str.clone(),
                    });
                    *pending_op = None;
                } else if mode.is_hard() {
                    return Err(unresolved_pending_error("operator", pending));
                }
            }
            if mode.is_hard() {
                drain_pending(pending_dict_args, dict_args, "call", resolve)?;
            } else {
                drain_pending_lenient(pending_dict_args, dict_args, resolve);
            }
            resolve_dict_uses_expr_with_mode(lhs, resolve, process_fn, mode)?;
            resolve_dict_uses_expr_with_mode(rhs, resolve, process_fn, mode)?;
            Ok(())
        }
        ExprKind::Neg {
            operand,
            resolved_op,
            pending_op,
            ..
        } => {
            if let Some(pending) = pending_op.as_ref() {
                if let Some(dict) = resolve(pending) {
                    *resolved_op = Some(ResolvedCallee::DictMethod {
                        dict,
                        method: "-".to_string(),
                    });
                    *pending_op = None;
                } else if mode.is_hard() {
                    return Err(unresolved_pending_error("operator", pending));
                }
            }
            resolve_dict_uses_expr_with_mode(operand, resolve, process_fn, mode)?;
            Ok(())
        }
        ExprKind::Call {
            callee,
            args,
            arg_wrappers,
            resolved_callee,
            pending_trait_method,
            dict_args,
            pending_dict_args,
            ..
        } => {
            if let Some((pending, method_name)) = pending_trait_method.take() {
                if let Some(dict) = resolve(&pending) {
                    *resolved_callee = Some(ResolvedCallee::DictMethod {
                        dict,
                        method: method_name.clone(),
                    });
                } else {
                    if mode.is_hard() {
                        return Err(TypeError::UnresolvedTrait {
                            context: "method call".to_string(),
                            trait_name: pending.trait_name.clone(),
                        });
                    }
                    *pending_trait_method = Some((pending, method_name));
                }
            }
            if mode.is_hard() {
                drain_pending(pending_dict_args, dict_args, "call", resolve)?;
            } else {
                drain_pending_lenient(pending_dict_args, dict_args, resolve);
            }
            for wrapper in arg_wrappers.iter_mut().flatten() {
                drain_pending_lenient(
                    &mut wrapper.pending_dict_args,
                    &mut wrapper.dict_args,
                    resolve,
                );
            }
            resolve_dict_uses_expr_with_mode(callee, resolve, process_fn, mode)?;
            for arg in args {
                resolve_dict_uses_expr_with_mode(arg, resolve, process_fn, mode)?;
            }
            Ok(())
        }
        ExprKind::Block { stmts, final_expr } => {
            for stmt in stmts {
                resolve_dict_uses_stmt_inner_with_mode(stmt, resolve, process_fn, mode)?;
            }
            if let Some(e) = final_expr {
                resolve_dict_uses_expr_with_mode(e, resolve, process_fn, mode)?;
            }
            Ok(())
        }
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
        } => {
            resolve_dict_uses_expr_with_mode(cond, resolve, process_fn, mode)?;
            resolve_dict_uses_expr_with_mode(then_branch, resolve, process_fn, mode)?;
            resolve_dict_uses_expr_with_mode(else_branch, resolve, process_fn, mode)?;
            Ok(())
        }
        ExprKind::Lambda { body, .. } => {
            resolve_dict_uses_expr_with_mode(body, resolve, process_fn, mode)
        }
        ExprKind::Match { scrutinee, arms } => {
            resolve_dict_uses_expr_with_mode(scrutinee, resolve, process_fn, mode)?;
            for (_, arm_expr) in arms {
                resolve_dict_uses_expr_with_mode(arm_expr, resolve, process_fn, mode)?;
            }
            Ok(())
        }
        ExprKind::Loop(body) => resolve_dict_uses_expr_with_mode(body, resolve, process_fn, mode),
        ExprKind::Assign { target, value } => {
            resolve_dict_uses_expr_with_mode(target, resolve, process_fn, mode)?;
            resolve_dict_uses_expr_with_mode(value, resolve, process_fn, mode)?;
            Ok(())
        }
        ExprKind::Range { start, end, .. } => {
            if let Some(start) = start {
                resolve_dict_uses_expr_with_mode(start, resolve, process_fn, mode)?;
            }
            if let Some(end) = end {
                resolve_dict_uses_expr_with_mode(end, resolve, process_fn, mode)?;
            }
            Ok(())
        }
        ExprKind::Not(e) => resolve_dict_uses_expr_with_mode(e, resolve, process_fn, mode),
        ExprKind::Break(Some(e)) | ExprKind::Return(Some(e)) => {
            resolve_dict_uses_expr_with_mode(e, resolve, process_fn, mode)
        }
        ExprKind::Tuple(es) => {
            for e in es {
                resolve_dict_uses_expr_with_mode(e, resolve, process_fn, mode)?;
            }
            Ok(())
        }
        ExprKind::Array(entries) => {
            for entry in entries {
                resolve_dict_uses_expr_with_mode(entry.expr_mut(), resolve, process_fn, mode)?;
            }
            Ok(())
        }
        ExprKind::Record(entries) => {
            for entry in entries {
                resolve_dict_uses_expr_with_mode(entry.expr_mut(), resolve, process_fn, mode)?;
            }
            Ok(())
        }
        ExprKind::FieldAccess { expr, .. } => {
            resolve_dict_uses_expr_with_mode(expr, resolve, process_fn, mode)
        }
        ExprKind::Index {
            receiver,
            key,
            resolved_callee,
            pending_trait_method,
            dict_args,
            pending_dict_args,
            ..
        } => {
            if let Some((pending, method_name)) = pending_trait_method.take() {
                if let Some(dict) = resolve(&pending) {
                    *resolved_callee = Some(ResolvedCallee::DictMethod {
                        dict,
                        method: method_name.clone(),
                    });
                } else {
                    if mode.is_hard() {
                        return Err(TypeError::UnresolvedTrait {
                            context: "index expression".to_string(),
                            trait_name: pending.trait_name.clone(),
                        });
                    }
                    *pending_trait_method = Some((pending, method_name));
                }
            }
            if mode.is_hard() {
                drain_pending(pending_dict_args, dict_args, "index expression", resolve)?;
            } else {
                drain_pending_lenient(pending_dict_args, dict_args, resolve);
            }
            resolve_dict_uses_expr_with_mode(receiver, resolve, process_fn, mode)?;
            resolve_dict_uses_expr_with_mode(key, resolve, process_fn, mode)?;
            Ok(())
        }
        ExprKind::For {
            iterable,
            body,
            resolved_iter,
            pending_iter,
            ..
        } => {
            if let Some(pending) = pending_iter.as_ref() {
                if let Some(dict) = resolve(pending) {
                    *resolved_iter = Some(ResolvedCallee::DictMethod {
                        dict,
                        method: "iter".to_string(),
                    });
                    *pending_iter = None;
                } else if mode.is_hard() {
                    return Err(TypeError::UnresolvedTrait {
                        context: "iterator".to_string(),
                        trait_name: pending.trait_name.clone(),
                    });
                }
            }
            resolve_dict_uses_expr_with_mode(iterable, resolve, process_fn, mode)?;
            resolve_dict_uses_expr_with_mode(body, resolve, process_fn, mode)?;
            Ok(())
        }
        ExprKind::Import(_) => Ok(()),
        _ => Ok(()),
    }
}

fn resolve_dict_uses_stmt_inner(
    stmt: &mut Stmt,
    resolve: &impl Fn(&PendingDictArg) -> Option<DictRef>,
    process_fn: bool,
) -> Result<(), TypeError> {
    resolve_dict_uses_stmt_inner_with_mode(
        stmt,
        resolve,
        process_fn,
        DictResolveMode::HardUnresolved,
    )
}

fn resolve_dict_uses_stmt_inner_with_mode(
    stmt: &mut Stmt,
    resolve: &impl Fn(&PendingDictArg) -> Option<DictRef>,
    process_fn: bool,
    mode: DictResolveMode,
) -> Result<(), TypeError> {
    match stmt {
        Stmt::Fn { body, .. } | Stmt::Op { body, .. } => {
            if process_fn {
                resolve_dict_uses_expr_with_mode(body, resolve, process_fn, mode)
            } else {
                Ok(()) // handled during that function's own inference
            }
        }
        Stmt::Let { value, .. } => {
            resolve_dict_uses_expr_with_mode(value, resolve, process_fn, mode)
        }
        Stmt::Expr(e) => resolve_dict_uses_expr_with_mode(e, resolve, process_fn, mode),
        Stmt::Impl(id) => {
            for method in &mut id.methods {
                resolve_dict_uses_expr_with_mode(&mut method.body, resolve, process_fn, mode)?;
            }
            Ok(())
        }
        Stmt::InherentImpl(id) => {
            for method in &mut id.methods {
                resolve_dict_uses_expr_with_mode(&mut method.body, resolve, process_fn, mode)?;
            }
            Ok(())
        }
        Stmt::RecBlock { stmts, .. } => {
            for stmt in stmts {
                resolve_dict_uses_stmt_inner_with_mode(stmt, resolve, process_fn, mode)?;
            }
            Ok(())
        }
        _ => Ok(()),
    }
}

/// Final global pass: resolves remaining pending dict args using the fully
/// completed substitution. Called once per top-level statement after all
/// inference is done.
pub(super) fn final_pass_stmt(
    stmt: &mut Stmt,
    resolve: &impl Fn(&PendingDictArg) -> Option<DictRef>,
) -> Result<(), TypeError> {
    resolve_dict_uses_stmt_inner(stmt, resolve, true)
}

fn drain_pending(
    pending: &mut Vec<PendingDictArg>,
    resolved: &mut Vec<DictRef>,
    context: &str,
    resolve: &impl Fn(&PendingDictArg) -> Option<DictRef>,
) -> Result<(), TypeError> {
    let names: Result<Vec<_>, _> = pending
        .iter()
        .map(|p| resolve(p).ok_or_else(|| unresolved_pending_error(context, p)))
        .collect();
    resolved.extend(names?);
    pending.clear();
    Ok(())
}

fn unresolved_pending_error(context: &str, pending: &PendingDictArg) -> TypeError {
    let determinant_args = pending
        .determinant_indexes
        .iter()
        .filter_map(|index| pending.args.get(*index))
        .collect::<Vec<_>>();
    if !determinant_args.is_empty()
        && determinant_args
            .iter()
            .all(|arg| free_type_vars(arg).is_empty())
    {
        return TypeError::MissingTraitImpl {
            trait_name: pending.trait_name.clone(),
            impl_target: determinant_args
                .iter()
                .map(|arg| arg.to_string())
                .collect::<Vec<_>>()
                .join(", "),
        };
    }

    TypeError::UnresolvedTrait {
        context: context.to_string(),
        trait_name: pending.trait_name.clone(),
    }
}

fn drain_pending_lenient(
    pending: &mut Vec<PendingDictArg>,
    resolved: &mut Vec<DictRef>,
    resolve: &impl Fn(&PendingDictArg) -> Option<DictRef>,
) {
    let mut unresolved = Vec::new();
    for item in pending.drain(..) {
        if let Some(name) = resolve(&item) {
            resolved.push(name);
        } else {
            unresolved.push(item);
        }
    }
    *pending = unresolved;
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::{FuncParam, FuncReturn, Row};

    #[test]
    fn scheme_target_binding_tries_later_methods_when_earlier_method_is_incomplete() {
        let scheme = Scheme {
            vars: vec![0],
            constraints: vec![TraitConstraint::unary(0, "Show".to_string())],
            ty: Ty::Record(Row {
                fields: vec![
                    (
                        "first".to_string(),
                        Ty::Func(
                            vec![FuncParam::value(Ty::Con("Input".to_string()))],
                            FuncReturn::value(Ty::Int),
                        ),
                    ),
                    (
                        "second".to_string(),
                        Ty::Func(
                            vec![FuncParam::value(Ty::Con("Input".to_string()))],
                            FuncReturn::value(Ty::Var(0)),
                        ),
                    ),
                ],
                tail: Box::new(Ty::Unit),
            }),
        };
        let known_impl_dicts = HashSet::from(["__Show__string".to_string()]);

        let dict_args = dict_ref_args_for_scheme_args(
            &scheme,
            &[Ty::Con("Input".to_string()), Ty::Con("string".to_string())],
            &TypeEnv::new(),
            &known_impl_dicts,
            &HashMap::new(),
        )
        .expect("later method should provide the constrained variable binding");

        assert!(matches!(
            dict_args.as_slice(),
            [DictRef::Concrete(name)] if name == "__Show__string"
        ));
    }

    #[test]
    fn scheme_target_binding_combines_compatible_method_bindings() {
        let scheme = Scheme {
            vars: vec![0, 1],
            constraints: vec![
                TraitConstraint::unary(0, "Show".to_string()),
                TraitConstraint::unary(1, "Eq".to_string()),
            ],
            ty: Ty::Record(Row {
                fields: vec![
                    (
                        "first".to_string(),
                        Ty::Func(
                            vec![FuncParam::value(Ty::Con("Input".to_string()))],
                            FuncReturn::value(Ty::Var(0)),
                        ),
                    ),
                    (
                        "second".to_string(),
                        Ty::Func(
                            vec![FuncParam::value(Ty::Con("Input".to_string()))],
                            FuncReturn::value(Ty::Var(1)),
                        ),
                    ),
                ],
                tail: Box::new(Ty::Unit),
            }),
        };
        let known_impl_dicts =
            HashSet::from(["__Show__string".to_string(), "__Eq__string".to_string()]);

        let dict_args = dict_ref_args_for_scheme_args(
            &scheme,
            &[Ty::Con("Input".to_string()), Ty::Con("string".to_string())],
            &TypeEnv::new(),
            &known_impl_dicts,
            &HashMap::new(),
        )
        .expect("compatible methods should jointly bind constrained variables");

        assert!(matches!(
            dict_args.as_slice(),
            [DictRef::Concrete(show), DictRef::Concrete(eq)]
                if show == "__Show__string" && eq == "__Eq__string"
        ));
    }

    #[test]
    fn scheme_target_binding_uses_trait_args_not_full_method_arity() {
        let scheme = Scheme {
            vars: vec![0],
            constraints: vec![TraitConstraint::unary(0, "Eq".to_string())],
            ty: Ty::Record(Row {
                fields: vec![(
                    "==".to_string(),
                    Ty::Func(
                        vec![
                            FuncParam::value(Ty::App(
                                Box::new(Ty::Con("Box".to_string())),
                                vec![Ty::Var(0)],
                            )),
                            FuncParam::value(Ty::App(
                                Box::new(Ty::Con("Box".to_string())),
                                vec![Ty::Var(0)],
                            )),
                        ],
                        FuncReturn::value(Ty::Con("bool".to_string())),
                    ),
                )],
                tail: Box::new(Ty::Unit),
            }),
        };
        let known_impl_dicts = HashSet::from(["__Eq__int".to_string()]);

        let dict_args = dict_ref_args_for_scheme_args(
            &scheme,
            &[Ty::App(Box::new(Ty::Con("Box".to_string())), vec![Ty::Int])],
            &TypeEnv::new(),
            &known_impl_dicts,
            &HashMap::new(),
        )
        .expect("unary trait target should bind through the first method parameter");

        assert!(matches!(
            dict_args.as_slice(),
            [DictRef::Concrete(name)] if name == "__Eq__int"
        ));
    }
}
