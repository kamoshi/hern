use crate::ast::{Expr, ExprKind};

pub fn is_value(expr: &Expr) -> bool {
    match &expr.kind {
        ExprKind::Number(_)
        | ExprKind::StringLit(_)
        | ExprKind::Bool(_)
        | ExprKind::Ident(_)
        | ExprKind::Lambda { .. }
        | ExprKind::Import(_)
        | ExprKind::Unit => true,
        ExprKind::Tuple(exprs) => exprs.iter().all(is_value),
        ExprKind::Array(entries) => entries.iter().all(|e| is_value(e.expr())),
        ExprKind::Record(entries) => entries.iter().all(|e| is_value(e.expr())),
        _ => false,
    }
}

pub fn is_fresh_mutable_place(expr: &Expr) -> bool {
    match &expr.kind {
        // Array elements are safe to alias: extraction via .get() returns 'a (not mut 'a),
        // so callers cannot mutate elements through the array.
        ExprKind::Array(entries) => entries.iter().all(|e| is_fresh_array_element(e.expr())),
        // Record fields are NOT safe to alias via identifiers: field access on a mutable
        // record reaches straight into the Lua table, allowing mutation of the original.
        ExprKind::Record(entries) => entries.iter().all(|e| is_fresh_mutable_component(e.expr())),
        _ => false,
    }
}

fn is_fresh_array_element(expr: &Expr) -> bool {
    matches!(expr.kind, ExprKind::Ident(_)) || is_fresh_mutable_component(expr)
}

fn is_fresh_mutable_component(expr: &Expr) -> bool {
    match &expr.kind {
        ExprKind::Number(_)
        | ExprKind::StringLit(_)
        | ExprKind::Bool(_)
        | ExprKind::Lambda { .. }
        | ExprKind::Unit => true,
        ExprKind::Tuple(exprs) => exprs.iter().all(is_fresh_mutable_component),
        ExprKind::Record(entries) => entries
            .iter()
            .all(|e| is_fresh_mutable_component(e.expr())),
        ExprKind::Array(entries) => entries
            .iter()
            .all(|e| is_fresh_array_element(e.expr())),
        _ => false,
    }
}
