use crate::ast::*;
use crate::types::{
    Scheme, Subst, TraitConstraint, Ty, TypeEnv,
    error::TypeError,
    perf,
    type_syntax::{
        trait_impl_arg_key_candidates_from_ty, trait_impl_dict_name_from_keys,
        trait_impl_target_keys_from_ty,
    },
    unify,
};
use std::collections::{HashMap, HashSet};

pub(super) fn dict_param_name(constraint: &TraitConstraint) -> String {
    format!("__dict_{}_{}", constraint.trait_name, constraint.var)
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
    if let Ty::Var(var) = resolved {
        constraints
            .iter()
            .find(|c| c.var == var && c.trait_name == pending.trait_name)
            .map(|constraint| DictRef::Param(dict_param_name(constraint)))
    } else {
        None
    }
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
            return None;
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
    if actual_args.is_empty() || params.len() > actual_args.len() {
        return false;
    }
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
    resolve_dict_uses_expr_with_mode(expr, resolve, process_fn, true)
}

pub(super) fn resolve_dict_uses_expr_lenient(
    expr: &mut Expr,
    resolve: &impl Fn(&PendingDictArg) -> Option<DictRef>,
    process_fn: bool,
) -> Result<(), TypeError> {
    resolve_dict_uses_expr_with_mode(expr, resolve, process_fn, false)
}

fn resolve_dict_uses_expr_with_mode(
    expr: &mut Expr,
    resolve: &impl Fn(&PendingDictArg) -> Option<DictRef>,
    process_fn: bool,
    hard_unresolved: bool,
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
                } else if hard_unresolved {
                    return Err(TypeError::UnresolvedTrait {
                        context: "operator".to_string(),
                        trait_name: pending.trait_name.clone(),
                    });
                }
            }
            if hard_unresolved {
                drain_pending(pending_dict_args, dict_args, "call", resolve)?;
            } else {
                drain_pending_lenient(pending_dict_args, dict_args, resolve);
            }
            resolve_dict_uses_expr_with_mode(lhs, resolve, process_fn, hard_unresolved)?;
            resolve_dict_uses_expr_with_mode(rhs, resolve, process_fn, hard_unresolved)?;
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
                    if hard_unresolved {
                        return Err(TypeError::UnresolvedTrait {
                            context: "method call".to_string(),
                            trait_name: pending.trait_name.clone(),
                        });
                    }
                    *pending_trait_method = Some((pending, method_name));
                }
            }
            if hard_unresolved {
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
            resolve_dict_uses_expr_with_mode(callee, resolve, process_fn, hard_unresolved)?;
            for arg in args {
                resolve_dict_uses_expr_with_mode(arg, resolve, process_fn, hard_unresolved)?;
            }
            Ok(())
        }
        ExprKind::Block { stmts, final_expr } => {
            for stmt in stmts {
                resolve_dict_uses_stmt_inner_with_mode(stmt, resolve, process_fn, hard_unresolved)?;
            }
            if let Some(e) = final_expr {
                resolve_dict_uses_expr_with_mode(e, resolve, process_fn, hard_unresolved)?;
            }
            Ok(())
        }
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
        } => {
            resolve_dict_uses_expr_with_mode(cond, resolve, process_fn, hard_unresolved)?;
            resolve_dict_uses_expr_with_mode(then_branch, resolve, process_fn, hard_unresolved)?;
            resolve_dict_uses_expr_with_mode(else_branch, resolve, process_fn, hard_unresolved)?;
            Ok(())
        }
        ExprKind::Lambda { body, .. } => {
            resolve_dict_uses_expr_with_mode(body, resolve, process_fn, hard_unresolved)
        }
        ExprKind::Match { scrutinee, arms } => {
            resolve_dict_uses_expr_with_mode(scrutinee, resolve, process_fn, hard_unresolved)?;
            for (_, arm_expr) in arms {
                resolve_dict_uses_expr_with_mode(arm_expr, resolve, process_fn, hard_unresolved)?;
            }
            Ok(())
        }
        ExprKind::Loop(body) => {
            resolve_dict_uses_expr_with_mode(body, resolve, process_fn, hard_unresolved)
        }
        ExprKind::Assign { target, value } => {
            resolve_dict_uses_expr_with_mode(target, resolve, process_fn, hard_unresolved)?;
            resolve_dict_uses_expr_with_mode(value, resolve, process_fn, hard_unresolved)?;
            Ok(())
        }
        ExprKind::Not(e) => {
            resolve_dict_uses_expr_with_mode(e, resolve, process_fn, hard_unresolved)
        }
        ExprKind::Break(Some(e)) | ExprKind::Return(Some(e)) => {
            resolve_dict_uses_expr_with_mode(e, resolve, process_fn, hard_unresolved)
        }
        ExprKind::Tuple(es) => {
            for e in es {
                resolve_dict_uses_expr_with_mode(e, resolve, process_fn, hard_unresolved)?;
            }
            Ok(())
        }
        ExprKind::Array(entries) => {
            for entry in entries {
                resolve_dict_uses_expr_with_mode(
                    entry.expr_mut(),
                    resolve,
                    process_fn,
                    hard_unresolved,
                )?;
            }
            Ok(())
        }
        ExprKind::Record(entries) => {
            for entry in entries {
                resolve_dict_uses_expr_with_mode(
                    entry.expr_mut(),
                    resolve,
                    process_fn,
                    hard_unresolved,
                )?;
            }
            Ok(())
        }
        ExprKind::FieldAccess { expr, .. } => {
            resolve_dict_uses_expr_with_mode(expr, resolve, process_fn, hard_unresolved)
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
                    if hard_unresolved {
                        return Err(TypeError::UnresolvedTrait {
                            context: "index expression".to_string(),
                            trait_name: pending.trait_name.clone(),
                        });
                    }
                    *pending_trait_method = Some((pending, method_name));
                }
            }
            if hard_unresolved {
                drain_pending(pending_dict_args, dict_args, "index expression", resolve)?;
            } else {
                drain_pending_lenient(pending_dict_args, dict_args, resolve);
            }
            resolve_dict_uses_expr_with_mode(receiver, resolve, process_fn, hard_unresolved)?;
            resolve_dict_uses_expr_with_mode(key, resolve, process_fn, hard_unresolved)?;
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
                } else if hard_unresolved {
                    return Err(TypeError::UnresolvedTrait {
                        context: "iterator".to_string(),
                        trait_name: pending.trait_name.clone(),
                    });
                }
            }
            resolve_dict_uses_expr_with_mode(iterable, resolve, process_fn, hard_unresolved)?;
            resolve_dict_uses_expr_with_mode(body, resolve, process_fn, hard_unresolved)?;
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
    resolve_dict_uses_stmt_inner_with_mode(stmt, resolve, process_fn, true)
}

fn resolve_dict_uses_stmt_inner_with_mode(
    stmt: &mut Stmt,
    resolve: &impl Fn(&PendingDictArg) -> Option<DictRef>,
    process_fn: bool,
    hard_unresolved: bool,
) -> Result<(), TypeError> {
    match stmt {
        Stmt::Fn { body, .. } | Stmt::Op { body, .. } => {
            if process_fn {
                resolve_dict_uses_expr_with_mode(body, resolve, process_fn, hard_unresolved)
            } else {
                Ok(()) // handled during that function's own inference
            }
        }
        Stmt::Let { value, .. } => {
            resolve_dict_uses_expr_with_mode(value, resolve, process_fn, hard_unresolved)
        }
        Stmt::Expr(e) => resolve_dict_uses_expr_with_mode(e, resolve, process_fn, hard_unresolved),
        Stmt::Impl(id) => {
            for method in &mut id.methods {
                resolve_dict_uses_expr_with_mode(
                    &mut method.body,
                    resolve,
                    process_fn,
                    hard_unresolved,
                )?;
            }
            Ok(())
        }
        Stmt::InherentImpl(id) => {
            for method in &mut id.methods {
                resolve_dict_uses_expr_with_mode(
                    &mut method.body,
                    resolve,
                    process_fn,
                    hard_unresolved,
                )?;
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
        .map(|p| {
            resolve(p).ok_or_else(|| TypeError::UnresolvedTrait {
                context: context.to_string(),
                trait_name: p.trait_name.clone(),
            })
        })
        .collect();
    resolved.extend(names?);
    pending.clear();
    Ok(())
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
}
