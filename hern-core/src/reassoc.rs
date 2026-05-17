use crate::ast::*;
use std::collections::{HashMap, VecDeque};

pub type FixityTable = HashMap<String, (Fixity, u8)>;

#[derive(Debug, Clone)]
pub struct ReassocError {
    pub span: SourceSpan,
    pub message: String,
}

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

pub fn reassoc_program(program: &mut Program, table: &FixityTable) -> Result<(), ReassocError> {
    let mut next_node_id = next_program_node_id(program);
    for stmt in &mut program.stmts {
        reassoc_stmt(stmt, table, &mut next_node_id)?;
    }
    Ok(())
}

fn reassoc_stmt(
    stmt: &mut Stmt,
    table: &FixityTable,
    next_node_id: &mut NodeId,
) -> Result<(), ReassocError> {
    match stmt {
        Stmt::Let { value, .. } => reassoc_expr_with_ids(value, table, next_node_id)?,
        Stmt::Fn { body, .. } | Stmt::Op { body, .. } => {
            reassoc_expr_with_ids(body, table, next_node_id)?
        }
        Stmt::Expr(e) => reassoc_expr_with_ids(e, table, next_node_id)?,
        Stmt::Impl(id) => {
            for m in &mut id.methods {
                reassoc_expr_with_ids(&mut m.body, table, next_node_id)?;
            }
        }
        Stmt::InherentImpl(id) => {
            for m in &mut id.methods {
                reassoc_expr_with_ids(&mut m.body, table, next_node_id)?;
            }
        }
        Stmt::TestBlock { stmts, .. } => {
            for stmt in stmts {
                reassoc_stmt(stmt, table, next_node_id)?;
            }
        }
        Stmt::RecBlock { stmts, .. } => {
            for stmt in stmts {
                reassoc_stmt(stmt, table, next_node_id)?;
            }
        }
        Stmt::Type(_) | Stmt::TypeAlias { .. } | Stmt::Trait(_) | Stmt::Extern { .. } => {}
    }
    Ok(())
}

#[cfg(test)]
fn reassoc_expr(expr: &mut Expr, table: &FixityTable) -> Result<(), ReassocError> {
    let mut next_node_id = max_expr_node_id(expr).saturating_add(1).max(1);
    reassoc_expr_with_ids(expr, table, &mut next_node_id)
}

fn reassoc_expr_with_ids(
    expr: &mut Expr,
    table: &FixityTable,
    next_node_id: &mut NodeId,
) -> Result<(), ReassocError> {
    // If this is a custom-op binary chain, flatten and re-Pratt it.
    if is_custom_binary(expr) {
        let owned = expr.clone();
        let mut parts: VecDeque<(String, SourceSpan, Expr)> = VecDeque::new();
        let head = flatten(owned, &mut parts);
        // Reassoc atoms
        let head = reassoc_owned(head, table, next_node_id)?;
        let parts: VecDeque<(String, SourceSpan, Expr)> = parts
            .into_iter()
            .map(|(op, op_span, e)| {
                reassoc_owned(e, table, next_node_id).map(|e| (op, op_span, e))
            })
            .collect::<Result<_, _>>()?;
        validate_operator_chain(&parts, table)?;
        *expr = pratt(head, &mut { parts }, 0, table, next_node_id);
        return Ok(());
    }

    // Otherwise recurse into sub-expressions.
    match &mut expr.kind {
        ExprKind::Grouped(e) | ExprKind::Not(e) => reassoc_expr_with_ids(e, table, next_node_id)?,
        ExprKind::Neg { operand, .. } => reassoc_expr_with_ids(operand, table, next_node_id)?,
        ExprKind::Assign { target, value } => {
            reassoc_expr_with_ids(target, table, next_node_id)?;
            reassoc_expr_with_ids(value, table, next_node_id)?;
        }
        ExprKind::Binary { lhs, rhs, .. } => {
            reassoc_expr_with_ids(lhs, table, next_node_id)?;
            reassoc_expr_with_ids(rhs, table, next_node_id)?;
        }
        ExprKind::Range { start, end, .. } => {
            if let Some(start) = start {
                reassoc_expr_with_ids(start, table, next_node_id)?;
            }
            if let Some(end) = end {
                reassoc_expr_with_ids(end, table, next_node_id)?;
            }
        }
        ExprKind::Call { callee, args, .. } => {
            reassoc_expr_with_ids(callee, table, next_node_id)?;
            for a in args {
                reassoc_expr_with_ids(a, table, next_node_id)?;
            }
        }
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
        } => {
            reassoc_expr_with_ids(cond, table, next_node_id)?;
            reassoc_expr_with_ids(then_branch, table, next_node_id)?;
            reassoc_expr_with_ids(else_branch, table, next_node_id)?;
        }
        ExprKind::Match { scrutinee, arms } => {
            reassoc_expr_with_ids(scrutinee, table, next_node_id)?;
            for (_, body) in arms {
                reassoc_expr_with_ids(body, table, next_node_id)?;
            }
        }
        ExprKind::Loop(body) => reassoc_expr_with_ids(body, table, next_node_id)?,
        ExprKind::Break(val) => {
            if let Some(e) = val {
                reassoc_expr_with_ids(e, table, next_node_id)?;
            }
        }
        ExprKind::Return(val) => {
            if let Some(e) = val {
                reassoc_expr_with_ids(e, table, next_node_id)?;
            }
        }
        ExprKind::Block { stmts, final_expr } => {
            for s in stmts {
                reassoc_stmt(s, table, next_node_id)?;
            }
            if let Some(e) = final_expr {
                reassoc_expr_with_ids(e, table, next_node_id)?;
            }
        }
        ExprKind::Tuple(es) => {
            for e in es {
                reassoc_expr_with_ids(e, table, next_node_id)?;
            }
        }
        ExprKind::Array(entries) => {
            for entry in entries {
                reassoc_expr_with_ids(entry.expr_mut(), table, next_node_id)?;
            }
        }
        ExprKind::Record(entries) => {
            for entry in entries {
                reassoc_expr_with_ids(entry.expr_mut(), table, next_node_id)?;
            }
        }
        ExprKind::FieldAccess { expr, .. } => {
            reassoc_expr_with_ids(expr, table, next_node_id)?
        }
        ExprKind::Index { receiver, key, .. } => {
            reassoc_expr_with_ids(receiver, table, next_node_id)?;
            reassoc_expr_with_ids(key, table, next_node_id)?;
        }
        ExprKind::AssociatedAccess { .. } => {}
        ExprKind::Lambda { body, .. } => reassoc_expr_with_ids(body, table, next_node_id)?,
        ExprKind::For { iterable, body, .. } => {
            reassoc_expr_with_ids(iterable, table, next_node_id)?;
            reassoc_expr_with_ids(body, table, next_node_id)?;
        }
        ExprKind::Number(_)
        | ExprKind::StringLit(_)
        | ExprKind::Bool(_)
        | ExprKind::Ident(_)
        | ExprKind::Import(_)
        | ExprKind::Unit
        | ExprKind::Continue => {}
    }
    Ok(())
}

fn reassoc_owned(
    expr: Expr,
    table: &FixityTable,
    next_node_id: &mut NodeId,
) -> Result<Expr, ReassocError> {
    let mut e = expr;
    reassoc_expr_with_ids(&mut e, table, next_node_id)?;
    Ok(e)
}

fn next_program_node_id(program: &Program) -> NodeId {
    // NodeId is currently an expression-only identifier. If other AST nodes grow
    // NodeIds later, include them here before generating reassociation nodes.
    program
        .stmts
        .iter()
        .map(max_stmt_node_id)
        .max()
        .unwrap_or(0)
        .saturating_add(1)
        .max(1)
}

fn next_id(next_node_id: &mut NodeId) -> NodeId {
    let id = *next_node_id;
    *next_node_id = next_node_id.saturating_add(1);
    id
}

fn max_stmt_node_id(stmt: &Stmt) -> NodeId {
    match stmt {
        Stmt::Let { value, .. } | Stmt::Expr(value) => max_expr_node_id(value),
        Stmt::Fn { body, .. } | Stmt::Op { body, .. } => max_expr_node_id(body),
        Stmt::Impl(id) => id
            .methods
            .iter()
            .map(|method| max_expr_node_id(&method.body))
            .max()
            .unwrap_or(0),
        Stmt::InherentImpl(id) => id
            .methods
            .iter()
            .map(|method| max_expr_node_id(&method.body))
            .max()
            .unwrap_or(0),
        Stmt::TestBlock { stmts, .. } | Stmt::RecBlock { stmts, .. } => stmts
            .iter()
            .map(max_stmt_node_id)
            .max()
            .unwrap_or(0),
        Stmt::Type(_) | Stmt::TypeAlias { .. } | Stmt::Trait(_) | Stmt::Extern { .. } => 0,
    }
}

fn max_expr_node_id(expr: &Expr) -> NodeId {
    let child_max = match &expr.kind {
        ExprKind::Grouped(e)
        | ExprKind::Not(e)
        | ExprKind::Neg { operand: e, .. }
        | ExprKind::Loop(e)
        | ExprKind::Break(Some(e))
        | ExprKind::Return(Some(e))
        | ExprKind::FieldAccess { expr: e, .. }
        | ExprKind::Lambda { body: e, .. } => max_expr_node_id(e),
        ExprKind::Index { receiver, key, .. } => {
            max_expr_node_id(receiver).max(max_expr_node_id(key))
        }
        ExprKind::Assign { target, value } => {
            max_expr_node_id(target).max(max_expr_node_id(value))
        }
        ExprKind::Binary { lhs, rhs, .. } => max_expr_node_id(lhs).max(max_expr_node_id(rhs)),
        ExprKind::Range { start, end, .. } => start
            .as_deref()
            .map(max_expr_node_id)
            .unwrap_or(0)
            .max(end.as_deref().map(max_expr_node_id).unwrap_or(0)),
        ExprKind::Call { callee, args, .. } => args
            .iter()
            .map(max_expr_node_id)
            .fold(max_expr_node_id(callee), NodeId::max),
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
        } => max_expr_node_id(cond)
            .max(max_expr_node_id(then_branch))
            .max(max_expr_node_id(else_branch)),
        ExprKind::Match { scrutinee, arms } => arms
            .iter()
            .map(|(_, body)| max_expr_node_id(body))
            .fold(max_expr_node_id(scrutinee), NodeId::max),
        ExprKind::Block { stmts, final_expr } => stmts
            .iter()
            .map(max_stmt_node_id)
            .chain(final_expr.as_deref().map(max_expr_node_id))
            .max()
            .unwrap_or(0),
        ExprKind::Tuple(items) => items.iter().map(max_expr_node_id).max().unwrap_or(0),
        ExprKind::Array(entries) => entries
            .iter()
            .map(|entry| max_expr_node_id(entry.expr()))
            .max()
            .unwrap_or(0),
        ExprKind::Record(entries) => entries
            .iter()
            .map(|entry| max_expr_node_id(entry.expr()))
            .max()
            .unwrap_or(0),
        ExprKind::For { iterable, body, .. } => {
            max_expr_node_id(iterable).max(max_expr_node_id(body))
        }
        ExprKind::Number(_)
        | ExprKind::StringLit(_)
        | ExprKind::Bool(_)
        | ExprKind::Ident(_)
        | ExprKind::Import(_)
        | ExprKind::Unit
        | ExprKind::Break(None)
        | ExprKind::Continue
        | ExprKind::Return(None)
        | ExprKind::AssociatedAccess { .. } => 0,
    };
    expr.id.max(child_max)
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

fn validate_operator_chain(
    tail: &VecDeque<(String, SourceSpan, Expr)>,
    table: &FixityTable,
) -> Result<(), ReassocError> {
    for idx in 1..tail.len() {
        let (left_op, _, _) = &tail[idx - 1];
        let (right_op, right_span, _) = &tail[idx];
        let (left_fixity, left_prec) = fixity_for(left_op, table);
        let (right_fixity, right_prec) = fixity_for(right_op, table);
        if left_prec != right_prec {
            continue;
        }
        if left_fixity == Fixity::Non || right_fixity == Fixity::Non {
            return Err(ReassocError {
                span: *right_span,
                message: format!(
                    "cannot chain non-associative operators `{}` and `{}` at precedence {}",
                    left_op, right_op, left_prec
                ),
            });
        }
        if left_fixity != right_fixity {
            return Err(ReassocError {
                span: *right_span,
                message: format!(
                    "conflicting associativity for operators `{}` and `{}` at precedence {}",
                    left_op, right_op, left_prec
                ),
            });
        }
    }
    Ok(())
}

fn fixity_for(op: &str, table: &FixityTable) -> (Fixity, u8) {
    table.get(op).copied().unwrap_or((Fixity::Left, 6))
}

/// Pratt parser over a flat `(op, op_span, atom)` deque.
fn pratt(
    lhs: Expr,
    tail: &mut VecDeque<(String, SourceSpan, Expr)>,
    min_prec: u8,
    table: &FixityTable,
    next_node_id: &mut NodeId,
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
        let rhs = pratt(rhs_atom, tail, next_min, table, next_node_id);
        let span = SourceSpan {
            start_line: lhs.span.start_line,
            start_col: lhs.span.start_col,
            end_line: rhs.span.end_line,
            end_col: rhs.span.end_col,
        };
        lhs = Expr::new(
            next_id(next_node_id),
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

#[cfg(test)]
mod tests {
    use super::*;

    fn ident(name: &str) -> Expr {
        Expr::synthetic(ExprKind::Ident(name.to_string()))
    }

    fn binary(lhs: Expr, op: &str, rhs: Expr) -> Expr {
        Expr::synthetic(ExprKind::Binary {
            lhs: Box::new(lhs),
            op: BinOp::Custom(op.to_string()),
            op_span: SourceSpan::synthetic(),
            rhs: Box::new(rhs),
            resolved_op: None,
            pending_op: None,
            dict_args: vec![],
            pending_dict_args: vec![],
        })
    }

    fn grouped(expr: Expr) -> Expr {
        Expr::synthetic(ExprKind::Grouped(Box::new(expr)))
    }

    #[test]
    fn grouped_expression_is_reassociation_boundary() {
        let mut expr = binary(
            ident("a"),
            "**",
            grouped(binary(ident("b"), "++", ident("c"))),
        );
        let table = HashMap::from([
            ("**".to_string(), (Fixity::Left, 9)),
            ("++".to_string(), (Fixity::Left, 1)),
        ]);

        reassoc_expr(&mut expr, &table).expect("expression should reassociate");

        let ExprKind::Binary { lhs, op, rhs, .. } = &expr.kind else {
            panic!("expected outer binary expression");
        };
        assert!(matches!(lhs.kind, ExprKind::Ident(ref name) if name == "a"));
        assert!(matches!(op, BinOp::Custom(name) if name == "**"));
        let ExprKind::Grouped(grouped) = &rhs.kind else {
            panic!("expected grouped right-hand side to remain grouped");
        };
        assert!(matches!(
            &grouped.kind,
            ExprKind::Binary {
                op: BinOp::Custom(name),
                ..
            } if name == "++"
        ));
    }

    #[test]
    fn same_precedence_conflicting_associativity_errors() {
        let mut expr = binary(binary(ident("a"), "|++", ident("b")), "++|", ident("c"));
        let table = HashMap::from([
            ("|++".to_string(), (Fixity::Left, 5)),
            ("++|".to_string(), (Fixity::Right, 5)),
        ]);

        let err = reassoc_expr(&mut expr, &table).expect_err("conflict should fail");

        assert!(err.message.contains("conflicting associativity"));
        assert!(err.message.contains("`|++`"));
        assert!(err.message.contains("`++|`"));
    }
}
