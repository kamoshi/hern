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
