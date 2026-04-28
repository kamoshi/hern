use crate::ast::*;
use std::collections::{HashMap, VecDeque};

pub type FixityTable = HashMap<String, (Fixity, u8)>;

pub fn build_fixity_table(program: &Program) -> FixityTable {
    let mut table = FixityTable::new();
    for stmt in &program.stmts {
        match stmt {
            Stmt::Op {
                name, fixity, prec, ..
            } => {
                table.insert(name.clone(), (*fixity, *prec));
            }
            Stmt::Trait(td) => {
                for method in &td.methods {
                    if let Some((fixity, prec)) = method.fixity {
                        table.insert(method.name.clone(), (fixity, prec));
                    }
                }
            }
            _ => {}
        }
    }
    table
}

pub fn reassoc_program(program: &mut Program, table: &FixityTable) {
    for stmt in &mut program.stmts {
        reassoc_stmt(stmt, table);
    }
}

fn reassoc_stmt(stmt: &mut Stmt, table: &FixityTable) {
    match stmt {
        Stmt::Let { value, .. } => reassoc_expr(value, table),
        Stmt::Fn { body, .. } | Stmt::Op { body, .. } => reassoc_expr(body, table),
        Stmt::Expr(e) => reassoc_expr(e, table),
        Stmt::Impl(id) => {
            for m in &mut id.methods {
                reassoc_expr(&mut m.body, table);
            }
        }
        Stmt::Type(_) | Stmt::TypeAlias { .. } | Stmt::Trait(_) | Stmt::Extern { .. } => {}
    }
}

fn reassoc_expr(expr: &mut Expr, table: &FixityTable) {
    // If this is a custom-op binary chain, flatten and re-Pratt it.
    if is_custom_binary(expr) {
        let owned = std::mem::replace(expr, Expr::synthetic(ExprKind::Unit));
        let mut parts: VecDeque<(String, SourceSpan, Expr)> = VecDeque::new();
        let head = flatten(owned, &mut parts);
        // Reassoc atoms
        let head = reassoc_owned(head, table);
        let parts: VecDeque<(String, SourceSpan, Expr)> = parts
            .into_iter()
            .map(|(op, op_span, e)| (op, op_span, reassoc_owned(e, table)))
            .collect();
        *expr = pratt(head, &mut { parts }, 0, table);
        return;
    }

    // Otherwise recurse into sub-expressions.
    match &mut expr.kind {
        ExprKind::Not(e) => reassoc_expr(e, table),
        ExprKind::Assign { target, value } => {
            reassoc_expr(target, table);
            reassoc_expr(value, table);
        }
        ExprKind::Binary { lhs, rhs, .. } => {
            reassoc_expr(lhs, table);
            reassoc_expr(rhs, table);
        }
        ExprKind::Call { callee, args, .. } => {
            reassoc_expr(callee, table);
            for a in args {
                reassoc_expr(a, table);
            }
        }
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
        } => {
            reassoc_expr(cond, table);
            reassoc_expr(then_branch, table);
            reassoc_expr(else_branch, table);
        }
        ExprKind::Match { scrutinee, arms } => {
            reassoc_expr(scrutinee, table);
            for (_, body) in arms {
                reassoc_expr(body, table);
            }
        }
        ExprKind::Loop(body) => reassoc_expr(body, table),
        ExprKind::Break(val) => {
            if let Some(e) = val {
                reassoc_expr(e, table);
            }
        }
        ExprKind::Return(val) => {
            if let Some(e) = val {
                reassoc_expr(e, table);
            }
        }
        ExprKind::Block { stmts, final_expr } => {
            for s in stmts {
                reassoc_stmt(s, table);
            }
            if let Some(e) = final_expr {
                reassoc_expr(e, table);
            }
        }
        ExprKind::Tuple(es) | ExprKind::Array(es) => {
            for e in es {
                reassoc_expr(e, table);
            }
        }
        ExprKind::Record(fields) => {
            for (_, e) in fields {
                reassoc_expr(e, table);
            }
        }
        ExprKind::FieldAccess { expr, .. } => reassoc_expr(expr, table),
        ExprKind::Lambda { body, .. } => reassoc_expr(body, table),
        ExprKind::For { iterable, body, .. } => {
            reassoc_expr(iterable, table);
            reassoc_expr(body, table);
        }
        ExprKind::Number(_)
        | ExprKind::StringLit(_)
        | ExprKind::Bool(_)
        | ExprKind::Ident(_)
        | ExprKind::Import(_)
        | ExprKind::Unit
        | ExprKind::Continue => {}
    }
}

fn reassoc_owned(expr: Expr, table: &FixityTable) -> Expr {
    let mut e = expr;
    reassoc_expr(&mut e, table);
    e
}

fn is_custom_binary(expr: &Expr) -> bool {
    matches!(
        &expr.kind,
        ExprKind::Binary {
            op: BinOp::Custom(_),
            pending_op: None,
            ..
        }
    )
}

/// Flatten a chain of custom-op binaries into (head, [(op, op_span, atom), ...]).
/// Atoms are not recursed into here — that's done separately.
fn flatten(expr: Expr, tail: &mut VecDeque<(String, SourceSpan, Expr)>) -> Expr {
    let Expr { id, span, kind } = expr;
    match kind {
        ExprKind::Binary {
            lhs,
            op: BinOp::Custom(op),
            op_span,
            rhs,
            ..
        } => {
            let head = flatten(*lhs, tail);
            // rhs may itself be a chain (e.g. right-leaning after a previous reassoc)
            flatten_rhs(*rhs, op, op_span, tail);
            head
        }
        other => Expr {
            id,
            span,
            kind: other,
        },
    }
}

fn flatten_rhs(
    expr: Expr,
    incoming_op: String,
    incoming_op_span: SourceSpan,
    tail: &mut VecDeque<(String, SourceSpan, Expr)>,
) {
    let Expr { id, span, kind } = expr;
    match kind {
        ExprKind::Binary {
            lhs,
            op: BinOp::Custom(op),
            op_span,
            rhs,
            ..
        } => {
            tail.push_back((incoming_op, incoming_op_span, *lhs));
            flatten_rhs(*rhs, op, op_span, tail);
        }
        other => tail.push_back((
            incoming_op,
            incoming_op_span,
            Expr {
                id,
                span,
                kind: other,
            },
        )),
    }
}

/// Pratt parser over a flat `(op, op_span, atom)` deque.
fn pratt(
    lhs: Expr,
    tail: &mut VecDeque<(String, SourceSpan, Expr)>,
    min_prec: u8,
    table: &FixityTable,
) -> Expr {
    let mut lhs = lhs;
    while let Some((op, _, _)) = tail.front() {
        let prec = table.get(op.as_str()).map_or(6, |(_, p)| *p);
        if prec < min_prec {
            break;
        }

        // tail.front() was Some above so pop_front always succeeds.
        let (op, op_span, rhs_atom) = tail.pop_front().unwrap();
        let fixity = table.get(op.as_str()).map_or(Fixity::Left, |(f, _)| *f);
        let next_min = match fixity {
            Fixity::Left | Fixity::Non => prec + 1,
            Fixity::Right => prec,
        };
        let rhs = pratt(rhs_atom, tail, next_min, table);
        let span = SourceSpan {
            start_line: lhs.span.start_line,
            start_col: lhs.span.start_col,
            end_line: rhs.span.end_line,
            end_col: rhs.span.end_col,
        };
        lhs = Expr::new(
            0,
            span,
            ExprKind::Binary {
                lhs: Box::new(lhs),
                op: BinOp::Custom(op),
                op_span,
                rhs: Box::new(rhs),
                resolved_op: None,
                pending_op: None,
                dict_args: vec![],
                pending_dict_args: vec![],
            },
        );
    }
    lhs
}
