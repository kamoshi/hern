//! Lexical type rules for local bindings and statements.
//!
//! This module owns scope-local environment changes: `let` bindings, statement
//! sequencing, block results, and the let-generalization boundary between local
//! polymorphism and expression inference.

use crate::ast::{BinOp, Expr, ExprKind, Param, Pattern, Stmt};
use std::collections::{HashMap, HashSet};

pub(super) fn collect_unshadowed_direct_call_targets(
    expr: &Expr,
    indexes: &HashMap<&str, usize>,
) -> HashSet<usize> {
    let mut targets = HashSet::new();
    collect_expr(expr, indexes, &mut targets);
    targets
}

fn collect_expr(expr: &Expr, indexes: &HashMap<&str, usize>, targets: &mut HashSet<usize>) {
    match &expr.kind {
        ExprKind::Grouped(inner)
        | ExprKind::Not(inner)
        | ExprKind::Neg { operand: inner, .. }
        | ExprKind::Loop(inner)
        | ExprKind::Break(Some(inner))
        | ExprKind::Return(Some(inner))
        | ExprKind::FieldAccess { expr: inner, .. } => collect_expr(inner, indexes, targets),
        ExprKind::Assign { target, value } => {
            collect_expr(target, indexes, targets);
            collect_expr(value, indexes, targets);
        }
        ExprKind::Binary { lhs, op, rhs, .. } => {
            if matches!(op, BinOp::Pipe) {
                collect_direct_call_target(rhs, indexes, targets);
            }
            collect_expr(lhs, indexes, targets);
            collect_expr(rhs, indexes, targets);
        }
        ExprKind::Range { start, end, .. } => {
            if let Some(start) = start {
                collect_expr(start, indexes, targets);
            }
            if let Some(end) = end {
                collect_expr(end, indexes, targets);
            }
        }
        ExprKind::Call {
            callee,
            args,
            is_method_call,
            ..
        } => {
            if !*is_method_call {
                collect_direct_call_target(callee, indexes, targets);
            }
            collect_expr(callee, indexes, targets);
            for arg in args {
                collect_expr(arg, indexes, targets);
            }
        }
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
        } => {
            collect_expr(cond, indexes, targets);
            collect_expr(then_branch, indexes, targets);
            collect_expr(else_branch, indexes, targets);
        }
        ExprKind::Lambda { params, body, .. } => {
            let scoped_indexes = indexes_without_param_bindings(indexes, params);
            collect_expr(body, &scoped_indexes, targets);
        }
        ExprKind::Match { scrutinee, arms } => {
            collect_expr(scrutinee, indexes, targets);
            for (pat, body) in arms {
                let scoped_indexes = indexes_without_pattern(indexes, pat);
                collect_expr(body, &scoped_indexes, targets);
            }
        }
        ExprKind::Tuple(items) => {
            for item in items {
                collect_expr(item, indexes, targets);
            }
        }
        ExprKind::Array(entries) => {
            for entry in entries {
                collect_expr(entry.expr(), indexes, targets);
            }
        }
        ExprKind::Record(entries) => {
            for entry in entries {
                collect_expr(entry.expr(), indexes, targets);
            }
        }
        ExprKind::Index { receiver, key, .. } => {
            collect_expr(receiver, indexes, targets);
            collect_expr(key, indexes, targets);
        }
        ExprKind::For {
            pat,
            iterable,
            body,
            ..
        } => {
            collect_expr(iterable, indexes, targets);
            let scoped_indexes = indexes_without_pattern(indexes, pat);
            collect_expr(body, &scoped_indexes, targets);
        }
        ExprKind::Block { stmts, final_expr } => {
            let mut scoped_indexes = indexes.clone();
            for stmt in stmts {
                collect_stmt(stmt, &scoped_indexes, targets);
                remove_stmt_value_bindings(&mut scoped_indexes, stmt);
            }
            if let Some(final_expr) = final_expr {
                collect_expr(final_expr, &scoped_indexes, targets);
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

fn collect_stmt(stmt: &Stmt, indexes: &HashMap<&str, usize>, targets: &mut HashSet<usize>) {
    match stmt {
        Stmt::Let { value, .. } | Stmt::Expr(value) => collect_expr(value, indexes, targets),
        Stmt::TestBlock { stmts, .. } | Stmt::RecBlock { stmts, .. } => {
            for stmt in stmts {
                collect_stmt(stmt, indexes, targets);
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

fn collect_direct_call_target(
    expr: &Expr,
    indexes: &HashMap<&str, usize>,
    targets: &mut HashSet<usize>,
) {
    match &expr.kind {
        ExprKind::Ident(name) => {
            if let Some(idx) = indexes.get(name.as_str()) {
                targets.insert(*idx);
            }
        }
        ExprKind::Grouped(inner) => collect_direct_call_target(inner, indexes, targets),
        _ => {}
    }
}

fn indexes_without_param_bindings<'a>(
    indexes: &HashMap<&'a str, usize>,
    params: &[Param],
) -> HashMap<&'a str, usize> {
    let mut scoped = indexes.clone();
    for param in params {
        remove_pattern_value_bindings(&mut scoped, &param.pat);
    }
    scoped
}

fn indexes_without_pattern<'a>(
    indexes: &HashMap<&'a str, usize>,
    pat: &Pattern,
) -> HashMap<&'a str, usize> {
    let mut scoped = indexes.clone();
    remove_pattern_value_bindings(&mut scoped, pat);
    scoped
}

fn remove_stmt_value_bindings(indexes: &mut HashMap<&str, usize>, stmt: &Stmt) {
    match stmt {
        Stmt::Let { pat, .. } => remove_pattern_value_bindings(indexes, pat),
        Stmt::Fn { name, .. } | Stmt::Op { name, .. } | Stmt::Extern { name, .. } => {
            indexes.remove(name.as_str());
        }
        Stmt::TestBlock { .. }
        | Stmt::RecBlock { .. }
        | Stmt::Macro(_)
        | Stmt::Trait(_)
        | Stmt::Impl(_)
        | Stmt::InherentImpl(_)
        | Stmt::Type(_)
        | Stmt::TypeAlias { .. }
        | Stmt::Expr(_) => {}
    }
}

fn remove_pattern_value_bindings(indexes: &mut HashMap<&str, usize>, pat: &Pattern) {
    match pat {
        Pattern::Variable(name, _) => {
            indexes.remove(name.as_str());
        }
        Pattern::Tuple(items) => {
            for item in items {
                remove_pattern_value_bindings(indexes, item);
            }
        }
        Pattern::List { elements, rest } => {
            for element in elements {
                remove_pattern_value_bindings(indexes, element);
            }
            if let Some(Some((name, _))) = rest {
                indexes.remove(name.as_str());
            }
        }
        Pattern::Constructor {
            binding: Some(binding),
            ..
        } => remove_pattern_value_bindings(indexes, binding),
        Pattern::Record { fields, rest } => {
            for (_, name, _) in fields {
                indexes.remove(name.as_str());
            }
            if let Some(Some((name, _))) = rest {
                indexes.remove(name.as_str());
            }
        }
        Pattern::SyntaxQuote(pattern) => {
            let mut captures = Vec::new();
            crate::syntax::collect_syntax_pattern_captures(pattern, &mut captures);
            for capture in captures {
                indexes.remove(capture.name.as_str());
            }
        }
        Pattern::Wildcard
        | Pattern::StringLit(_)
        | Pattern::NumberLit(_)
        | Pattern::BoolLit(_)
        | Pattern::IntRange { .. }
        | Pattern::Constructor { binding: None, .. } => {}
    }
}
