use crate::ast::{ArrayEntry, Expr, ExprKind, RecordEntry};

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
    is_fresh_mutable_component(expr)
        && matches!(expr.kind, ExprKind::Record(_) | ExprKind::Array(_))
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
            .all(|entry| matches!(entry, RecordEntry::Field(_, value) if is_fresh_mutable_component(value))),
        ExprKind::Array(entries) => entries
            .iter()
            .all(|entry| matches!(entry, ArrayEntry::Elem(value) if is_fresh_mutable_component(value))),
        _ => false,
    }
}
