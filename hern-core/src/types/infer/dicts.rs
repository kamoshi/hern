use crate::ast::*;
use crate::codegen::lua::mangle_op;
use crate::types::{
    Subst, TraitConstraint, Ty, TypeEnv, error::TypeError, type_syntax::ty_target_name,
};
use std::collections::HashSet;

pub(super) fn dict_param_name(constraint: &TraitConstraint) -> String {
    format!("__dict_{}_{}", constraint.trait_name, constraint.var)
}

pub(super) fn attach_dict_args(
    env: &TypeEnv,
    known_impl_dicts: &HashSet<String>,
    dict_args: &mut Vec<DictRef>,
    pending_dict_args: &mut Vec<PendingDictArg>,
    pending_constraints: &mut Vec<TraitConstraint>,
    constraints: &[TraitConstraint],
    subst: &Subst,
) -> Result<(), TypeError> {
    for constraint in constraints {
        let resolved = subst.apply(&Ty::Var(constraint.var));
        if let Ty::Var(var) = resolved {
            pending_constraints.push(TraitConstraint {
                var,
                trait_name: constraint.trait_name.clone(),
            });
            pending_dict_args.push(PendingDictArg {
                var,
                trait_name: constraint.trait_name.clone(),
            });
        } else if let Some(dict_ref) =
            resolve_concrete_dict_ref(&constraint.trait_name, &resolved, env, known_impl_dicts)
        {
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
    target_name: &str,
) -> bool {
    let dict_name = format!("__{}__{}", trait_name, target_name);
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
    subst: &Subst,
) -> Option<DictRef> {
    resolve_local_dict_name(pending, constraints, subst)
        .or_else(|| resolve_concrete(pending, env, known_impl_dicts, subst))
}

pub(super) fn resolve_concrete(
    pending: &PendingDictArg,
    env: &TypeEnv,
    known_impl_dicts: &HashSet<String>,
    subst: &Subst,
) -> Option<DictRef> {
    let resolved = subst.apply(&Ty::Var(pending.var));
    resolve_concrete_dict_ref(&pending.trait_name, &resolved, env, known_impl_dicts)
}

pub(super) fn resolve_concrete_dict_ref(
    trait_name: &str,
    ty: &Ty,
    env: &TypeEnv,
    known_impl_dicts: &HashSet<String>,
) -> Option<DictRef> {
    if trait_name == "Eq"
        && let Ty::Tuple(items) = ty
    {
        let args = items
            .iter()
            .map(|item| resolve_concrete_dict_ref("Eq", item, env, known_impl_dicts))
            .collect::<Option<Vec<_>>>()?;
        return Some(DictRef::Structural(StructuralDictRef {
            trait_name: "Eq".to_string(),
            target: DictTarget::Tuple(items.len()),
            args,
        }));
    }
    let target_name = ty_target_name(ty)?;
    if !has_trait_impl(env, known_impl_dicts, trait_name, &target_name) {
        return None;
    }
    Some(DictRef::Concrete(format!(
        "__{}__{}",
        trait_name, target_name
    )))
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
                        method: mangle_op(op_str),
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
                        method: mangle_op(&method_name),
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
