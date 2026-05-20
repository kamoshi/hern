//! Post-inference AST walkers.
//!
//! Some lowering metadata is easiest to attach after inference has selected
//! dictionaries and resolved recursive/self calls. This module owns those AST
//! walks so expression inference stays focused on type rules.

use super::*;

pub(super) fn find_assignment_base_name(expr: &Expr) -> Option<String> {
    match &expr.kind {
        ExprKind::Grouped(expr) => find_assignment_base_name(expr),
        ExprKind::FieldAccess { expr, .. } => find_assignment_base_name(expr),
        ExprKind::Ident(name) => Some(name.clone()),
        _ => None,
    }
}

pub(super) fn expr_always_exits(expr: &Expr, include_bc: bool) -> bool {
    match &expr.kind {
        ExprKind::Return(_) => true,
        ExprKind::Break(_) | ExprKind::Continue => include_bc,
        ExprKind::Grouped(e) | ExprKind::Not(e) | ExprKind::FieldAccess { expr: e, .. } => {
            expr_always_exits(e, include_bc)
        }
        ExprKind::Binary { lhs, rhs, .. } => {
            expr_always_exits(lhs, include_bc) || expr_always_exits(rhs, include_bc)
        }
        ExprKind::Assign { target, value } => {
            expr_always_exits(target, include_bc) || expr_always_exits(value, include_bc)
        }
        ExprKind::Call { callee, args, .. } => {
            expr_always_exits(callee, include_bc)
                || args.iter().any(|arg| expr_always_exits(arg, include_bc))
        }
        ExprKind::Tuple(es) => es.iter().any(|expr| expr_always_exits(expr, include_bc)),
        ExprKind::Array(entries) => entries
            .iter()
            .any(|entry| expr_always_exits(entry.expr(), include_bc)),
        ExprKind::Record(entries) => entries
            .iter()
            .any(|entry| expr_always_exits(entry.expr(), include_bc)),
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            expr_always_exits(cond, include_bc)
                || expr_always_exits(then_branch, include_bc)
                    && expr_always_exits(else_branch, include_bc)
        }
        ExprKind::Match { scrutinee, arms } => {
            expr_always_exits(scrutinee, include_bc)
                || !arms.is_empty()
                    && arms
                        .iter()
                        .all(|(_, body)| expr_always_exits(body, include_bc))
        }
        ExprKind::Block { stmts, final_expr } => {
            for stmt in stmts {
                if stmt_always_exits(stmt, include_bc) {
                    return true;
                }
            }
            final_expr
                .as_ref()
                .is_some_and(|expr| expr_always_exits(expr, include_bc))
        }
        ExprKind::Loop(body) => expr_always_exits(body, false),
        ExprKind::For { iterable, .. } => expr_always_exits(iterable, include_bc),
        ExprKind::Import(_) | ExprKind::SyntaxQuote(_) | ExprKind::MacroCall { .. } => false,
        _ => false,
    }
}

pub(super) fn stmt_always_exits(stmt: &Stmt, include_bc: bool) -> bool {
    match stmt {
        Stmt::Expr(expr) | Stmt::Let { value: expr, .. } => expr_always_exits(expr, include_bc),
        _ => false,
    }
}

pub(super) fn attach_owned_dicts_to_recursive_self_calls(
    expr: &mut Expr,
    self_name: &str,
    owned_constraints: &[TraitConstraint],
) {
    let self_dict_args = owned_constraints
        .iter()
        .map(|constraint| DictRef::Param(dict_param_name(constraint)))
        .collect::<Vec<_>>();
    attach_owned_dicts_to_recursive_self_calls_inner(expr, self_name, &self_dict_args);
}

pub(super) fn attach_owned_dicts_to_recursive_self_calls_inner(
    expr: &mut Expr,
    self_name: &str,
    self_dict_args: &[DictRef],
) {
    match &mut expr.kind {
        ExprKind::Grouped(inner)
        | ExprKind::Not(inner)
        | ExprKind::Neg { operand: inner, .. }
        | ExprKind::Loop(inner)
        | ExprKind::Break(Some(inner))
        | ExprKind::Return(Some(inner))
        | ExprKind::FieldAccess { expr: inner, .. } => {
            attach_owned_dicts_to_recursive_self_calls_inner(inner, self_name, self_dict_args);
        }
        ExprKind::Assign { target, value } => {
            attach_owned_dicts_to_recursive_self_calls_inner(target, self_name, self_dict_args);
            attach_owned_dicts_to_recursive_self_calls_inner(value, self_name, self_dict_args);
        }
        ExprKind::Binary {
            lhs,
            op,
            rhs,
            dict_args,
            pending_dict_args,
            ..
        } => {
            if matches!(op, BinOp::Pipe)
                && expr_is_ident(rhs, self_name)
                && dict_args.is_empty()
                && pending_dict_args.is_empty()
            {
                dict_args.extend_from_slice(self_dict_args);
            }
            attach_owned_dicts_to_recursive_self_calls_inner(lhs, self_name, self_dict_args);
            attach_owned_dicts_to_recursive_self_calls_inner(rhs, self_name, self_dict_args);
        }
        ExprKind::Range { start, end, .. } => {
            if let Some(start) = start {
                attach_owned_dicts_to_recursive_self_calls_inner(start, self_name, self_dict_args);
            }
            if let Some(end) = end {
                attach_owned_dicts_to_recursive_self_calls_inner(end, self_name, self_dict_args);
            }
        }
        ExprKind::Call {
            callee,
            args,
            is_method_call,
            dict_args,
            pending_dict_args,
            ..
        } => {
            if !*is_method_call
                && expr_is_ident(callee, self_name)
                && dict_args.is_empty()
                && pending_dict_args.is_empty()
            {
                dict_args.extend_from_slice(self_dict_args);
            }
            attach_owned_dicts_to_recursive_self_calls_inner(callee, self_name, self_dict_args);
            for arg in args {
                attach_owned_dicts_to_recursive_self_calls_inner(arg, self_name, self_dict_args);
            }
        }
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
        } => {
            attach_owned_dicts_to_recursive_self_calls_inner(cond, self_name, self_dict_args);
            attach_owned_dicts_to_recursive_self_calls_inner(
                then_branch,
                self_name,
                self_dict_args,
            );
            attach_owned_dicts_to_recursive_self_calls_inner(
                else_branch,
                self_name,
                self_dict_args,
            );
        }
        ExprKind::Lambda { params, body, .. } => {
            if !params
                .iter()
                .any(|param| pattern_binds_name(&param.pat, self_name))
            {
                attach_owned_dicts_to_recursive_self_calls_inner(body, self_name, self_dict_args);
            }
        }
        ExprKind::Match { scrutinee, arms } => {
            attach_owned_dicts_to_recursive_self_calls_inner(scrutinee, self_name, self_dict_args);
            for (pat, body) in arms {
                if !pattern_binds_name(pat, self_name) {
                    attach_owned_dicts_to_recursive_self_calls_inner(
                        body,
                        self_name,
                        self_dict_args,
                    );
                }
            }
        }
        ExprKind::Tuple(items) => {
            for item in items {
                attach_owned_dicts_to_recursive_self_calls_inner(item, self_name, self_dict_args);
            }
        }
        ExprKind::Array(entries) => {
            for entry in entries {
                attach_owned_dicts_to_recursive_self_calls_inner(
                    entry.expr_mut(),
                    self_name,
                    self_dict_args,
                );
            }
        }
        ExprKind::Record(entries) => {
            for entry in entries {
                attach_owned_dicts_to_recursive_self_calls_inner(
                    entry.expr_mut(),
                    self_name,
                    self_dict_args,
                );
            }
        }
        ExprKind::Index { receiver, key, .. } => {
            attach_owned_dicts_to_recursive_self_calls_inner(receiver, self_name, self_dict_args);
            attach_owned_dicts_to_recursive_self_calls_inner(key, self_name, self_dict_args);
        }
        ExprKind::For {
            pat,
            iterable,
            body,
            ..
        } => {
            attach_owned_dicts_to_recursive_self_calls_inner(iterable, self_name, self_dict_args);
            if !pattern_binds_name(pat, self_name) {
                attach_owned_dicts_to_recursive_self_calls_inner(body, self_name, self_dict_args);
            }
        }
        ExprKind::Block { stmts, final_expr } => {
            let mut shadowed = false;
            for stmt in stmts {
                if !shadowed {
                    attach_owned_dicts_to_recursive_self_calls_in_stmt(
                        stmt,
                        self_name,
                        self_dict_args,
                    );
                }
                shadowed |= stmt_binds_name(stmt, self_name);
            }
            if !shadowed && let Some(final_expr) = final_expr {
                attach_owned_dicts_to_recursive_self_calls_inner(
                    final_expr,
                    self_name,
                    self_dict_args,
                );
            }
        }
        ExprKind::Number(_)
        | ExprKind::StringLit(_)
        | ExprKind::Bool(_)
        | ExprKind::SyntaxQuote(_)
        | ExprKind::MacroCall { .. }
        | ExprKind::Ident(_)
        | ExprKind::Unit
        | ExprKind::Import(_)
        | ExprKind::Break(None)
        | ExprKind::Continue
        | ExprKind::Return(None)
        | ExprKind::AssociatedAccess { .. } => {}
    }
}

pub(super) fn attach_owned_dicts_to_recursive_self_calls_in_stmt(
    stmt: &mut Stmt,
    self_name: &str,
    self_dict_args: &[DictRef],
) {
    match stmt {
        Stmt::Let { value, .. } | Stmt::Expr(value) => {
            attach_owned_dicts_to_recursive_self_calls_inner(value, self_name, self_dict_args);
        }
        Stmt::TestBlock { stmts, .. } => {
            for stmt in stmts {
                attach_owned_dicts_to_recursive_self_calls_in_stmt(stmt, self_name, self_dict_args);
            }
        }
        Stmt::RecBlock { stmts, .. } => {
            for stmt in stmts {
                attach_owned_dicts_to_recursive_self_calls_in_stmt(stmt, self_name, self_dict_args);
            }
        }
        Stmt::Fn { .. }
        | Stmt::Op { .. }
        | Stmt::Macro(_)
        | Stmt::Trait(_)
        | Stmt::Impl(_)
        | Stmt::InherentImpl(_)
        | Stmt::Type(_)
        | Stmt::TypeAlias { .. }
        | Stmt::Extern { .. } => {}
    }
}

pub(super) fn propagate_rec_block_constraints(stmts: &[Stmt], infos: &mut [RecFnInfo]) {
    let call_targets = collect_rec_block_call_targets(stmts, infos);
    let mut constraints = infos
        .iter()
        .map(|info| info.constraints.clone())
        .collect::<Vec<_>>();

    let mut changed = true;
    while changed {
        changed = false;
        for caller_idx in 0..constraints.len() {
            for &callee_idx in &call_targets[caller_idx] {
                let callee_constraints = constraints[callee_idx].clone();
                for constraint in callee_constraints {
                    if !constraints[caller_idx].contains(&constraint) {
                        constraints[caller_idx].push(constraint);
                        changed = true;
                    }
                }
            }
        }
    }

    for (info, constraints) in infos.iter_mut().zip(constraints) {
        info.constraints = constraints;
    }
}

pub(super) fn collect_rec_block_call_targets(
    stmts: &[Stmt],
    infos: &[RecFnInfo],
) -> Vec<Vec<usize>> {
    let indexes = infos
        .iter()
        .enumerate()
        .map(|(idx, info)| (info.name.as_str(), idx))
        .collect::<HashMap<_, _>>();

    let mut targets_by_fn = Vec::with_capacity(stmts.len());
    for stmt in stmts {
        let Stmt::Fn { body, .. } = stmt else {
            unreachable!("rec block was validated to contain only functions")
        };
        let targets = lexical::collect_unshadowed_direct_call_targets(body, &indexes);
        let mut targets = targets.into_iter().collect::<Vec<_>>();
        targets.sort_unstable();
        targets_by_fn.push(targets);
    }
    targets_by_fn
}

pub(super) fn stmt_binds_name(stmt: &Stmt, name: &str) -> bool {
    match stmt {
        Stmt::Let { pat, .. } => pattern_binds_name(pat, name),
        Stmt::Fn { name: bound, .. } | Stmt::Op { name: bound, .. } => bound == name,
        Stmt::Extern { name: bound, .. } => bound == name,
        Stmt::TestBlock { .. }
        | Stmt::RecBlock { .. }
        | Stmt::Macro(_)
        | Stmt::Trait(_)
        | Stmt::Impl(_)
        | Stmt::InherentImpl(_)
        | Stmt::Type(_)
        | Stmt::TypeAlias { .. }
        | Stmt::Expr(_) => false,
    }
}

pub(super) fn pattern_binds_name(pat: &Pattern, name: &str) -> bool {
    match pat {
        Pattern::Variable(bound, _) => bound == name,
        Pattern::Tuple(items) => items.iter().any(|item| pattern_binds_name(item, name)),
        Pattern::List { elements, rest } => {
            elements
                .iter()
                .any(|element| pattern_binds_name(element, name))
                || rest
                    .as_ref()
                    .and_then(|rest| rest.as_ref())
                    .is_some_and(|(bound, _)| bound == name)
        }
        Pattern::Constructor {
            binding: Some(binding),
            ..
        } => pattern_binds_name(binding, name),
        Pattern::Record { fields, rest } => {
            fields.iter().any(|(_, bound, _)| bound == name)
                || rest
                    .as_ref()
                    .and_then(|rest| rest.as_ref())
                    .is_some_and(|(bound, _)| bound == name)
        }
        Pattern::SyntaxQuote(pattern) => {
            let mut captures = Vec::new();
            crate::syntax::collect_syntax_pattern_captures(pattern, &mut captures);
            captures.iter().any(|capture| capture.name == name)
        }
        Pattern::Wildcard
        | Pattern::StringLit(_)
        | Pattern::NumberLit(_)
        | Pattern::BoolLit(_)
        | Pattern::IntRange { .. }
        | Pattern::Constructor { binding: None, .. } => false,
    }
}

pub(super) fn expr_is_ident(expr: &Expr, name: &str) -> bool {
    match &expr.kind {
        ExprKind::Ident(ident) => ident == name,
        ExprKind::Grouped(inner) => expr_is_ident(inner, name),
        _ => false,
    }
}
