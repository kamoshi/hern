//! Phase-1 executable core IR for macro bodies.
//!
//! Macro definitions are parsed and typechecked as ordinary Hern, then lowered
//! into this smaller IR before comptime execution. This module owns the
//! "supported macro-phase surface" decision: adding a Hern expression to macros
//! should mean adding an explicit lowering rule here, plus evaluator coverage.

use crate::ast::{ArrayEntry, BinOp, Expr, ExprKind, Pattern, RecordEntry, SourceSpan, Stmt};
use crate::lex::NumberLiteral;
use crate::syntax::SyntaxTemplate;

use super::diagnostics::MacroRuntimeError;

#[derive(Debug, Clone)]
pub(super) struct CoreBody {
    pub(super) expr: CoreExpr,
}

#[derive(Debug, Clone)]
pub(super) struct CoreFunction {
    pub(super) params: Vec<Pattern>,
    pub(super) body: CoreExpr,
}

#[derive(Debug, Clone)]
pub(super) struct CoreExpr {
    pub(super) span: SourceSpan,
    pub(super) kind: CoreExprKind,
}

#[derive(Debug, Clone)]
pub(super) enum CoreExprKind {
    Unit,
    Int(i32),
    Float(f64),
    Bool(bool),
    String(String),
    Ident(String),
    SyntaxQuote(SyntaxTemplate),
    Lambda {
        params: Vec<Pattern>,
        body: Box<CoreExpr>,
    },
    Grouped(Box<CoreExpr>),
    If {
        cond: Box<CoreExpr>,
        then_branch: Box<CoreExpr>,
        else_branch: Box<CoreExpr>,
    },
    Block {
        stmts: Vec<CoreStmt>,
        final_expr: Option<Box<CoreExpr>>,
    },
    Loop(Box<CoreExpr>),
    Break(Option<Box<CoreExpr>>),
    Assign {
        target: CoreAssignTarget,
        value: Box<CoreExpr>,
    },
    Match {
        scrutinee: Box<CoreExpr>,
        arms: Vec<(Pattern, CoreExpr)>,
    },
    Call {
        callee: CoreCallee,
        args: Vec<CoreExpr>,
    },
    Tuple(Vec<CoreExpr>),
    Array(Vec<CoreExpr>),
    Record(Vec<(String, CoreExpr)>),
    FieldAccess {
        receiver: Box<CoreExpr>,
        field: String,
        field_span: SourceSpan,
    },
    Index {
        receiver: Box<CoreExpr>,
        key: Box<CoreExpr>,
    },
    Binary {
        lhs: Box<CoreExpr>,
        op: CoreBinaryOp,
        rhs: Box<CoreExpr>,
    },
}

#[derive(Debug, Clone)]
pub(super) struct CoreStmt {
    pub(super) span: SourceSpan,
    pub(super) kind: CoreStmtKind,
}

#[derive(Debug, Clone)]
pub(super) enum CoreStmtKind {
    Let { pat: Pattern, value: CoreExpr },
    Expr(CoreExpr),
}

#[derive(Debug, Clone)]
pub(super) enum CoreCallee {
    Ident(String),
    Expr(Box<CoreExpr>),
    Method {
        receiver: Box<CoreExpr>,
        name: String,
        span: SourceSpan,
    },
}

#[derive(Debug, Clone)]
pub(super) enum CoreAssignTarget {
    Ident(String),
    Unsupported(SourceSpan),
}

#[derive(Debug, Clone, Copy)]
pub(super) enum CoreBinaryOp {
    Eq,
    NotEq,
    And,
    Or,
    Add,
    Sub,
    Lt,
    Le,
    Gt,
    Ge,
}

pub(super) fn lower_macro_body_to_core(expr: &Expr) -> Result<CoreBody, MacroRuntimeError> {
    Ok(CoreBody {
        expr: lower_expr(expr)?,
    })
}

pub(super) fn lower_macro_function_to_core(
    params: &[crate::ast::Param],
    body: &Expr,
) -> Result<CoreFunction, MacroRuntimeError> {
    Ok(CoreFunction {
        params: params.iter().map(|param| param.pat.clone()).collect(),
        body: lower_expr(body)?,
    })
}

fn lower_expr(expr: &Expr) -> Result<CoreExpr, MacroRuntimeError> {
    let kind = match &expr.kind {
        ExprKind::Unit => CoreExprKind::Unit,
        ExprKind::Number(NumberLiteral::Int(value)) => CoreExprKind::Int(*value),
        ExprKind::Number(NumberLiteral::Float(value)) => CoreExprKind::Float(*value),
        ExprKind::Bool(value) => CoreExprKind::Bool(*value),
        ExprKind::StringLit(value) => CoreExprKind::String(value.clone()),
        ExprKind::Ident(name) => CoreExprKind::Ident(name.clone()),
        ExprKind::SyntaxQuote(template) => CoreExprKind::SyntaxQuote(template.clone()),
        ExprKind::Lambda { params, body, .. } => CoreExprKind::Lambda {
            params: params.iter().map(|param| param.pat.clone()).collect(),
            body: Box::new(lower_expr(body)?),
        },
        ExprKind::Grouped(inner) => CoreExprKind::Grouped(Box::new(lower_expr(inner)?)),
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
        } => CoreExprKind::If {
            cond: Box::new(lower_expr(cond)?),
            then_branch: Box::new(lower_expr(then_branch)?),
            else_branch: Box::new(lower_expr(else_branch)?),
        },
        ExprKind::Block { stmts, final_expr } => CoreExprKind::Block {
            stmts: stmts
                .iter()
                .map(lower_stmt)
                .collect::<Result<Vec<_>, _>>()?,
            final_expr: final_expr
                .as_deref()
                .map(lower_expr)
                .transpose()?
                .map(Box::new),
        },
        ExprKind::Loop(body) => CoreExprKind::Loop(Box::new(lower_expr(body)?)),
        ExprKind::Break(value) => {
            CoreExprKind::Break(value.as_deref().map(lower_expr).transpose()?.map(Box::new))
        }
        ExprKind::Assign { target, value } => CoreExprKind::Assign {
            target: lower_assign_target(target),
            value: Box::new(lower_expr(value)?),
        },
        ExprKind::Match { scrutinee, arms } => CoreExprKind::Match {
            scrutinee: Box::new(lower_expr(scrutinee)?),
            arms: arms
                .iter()
                .map(|(pattern, body)| Ok((pattern.clone(), lower_expr(body)?)))
                .collect::<Result<Vec<_>, MacroRuntimeError>>()?,
        },
        ExprKind::Call { callee, args, .. } => CoreExprKind::Call {
            callee: lower_callee(callee)?,
            args: args.iter().map(lower_expr).collect::<Result<Vec<_>, _>>()?,
        },
        ExprKind::Array(entries) => CoreExprKind::Array(
            entries
                .iter()
                .map(lower_array_entry)
                .collect::<Result<Vec<_>, _>>()?,
        ),
        ExprKind::Tuple(items) => CoreExprKind::Tuple(
            items
                .iter()
                .map(lower_expr)
                .collect::<Result<Vec<_>, _>>()?,
        ),
        ExprKind::Record(entries) => CoreExprKind::Record(
            entries
                .iter()
                .map(lower_record_entry)
                .collect::<Result<Vec<_>, _>>()?,
        ),
        ExprKind::FieldAccess {
            expr,
            field,
            field_span,
        } => CoreExprKind::FieldAccess {
            receiver: Box::new(lower_expr(expr)?),
            field: field.clone(),
            field_span: *field_span,
        },
        ExprKind::Index { receiver, key, .. } => CoreExprKind::Index {
            receiver: Box::new(lower_expr(receiver)?),
            key: Box::new(lower_expr(key)?),
        },
        ExprKind::Binary { lhs, op, rhs, .. } => CoreExprKind::Binary {
            lhs: Box::new(lower_expr(lhs)?),
            op: lower_binary_op(op).ok_or_else(|| {
                MacroRuntimeError::new(expr.span, "unsupported macro-phase binary operator")
            })?,
            rhs: Box::new(lower_expr(rhs)?),
        },
        _ => {
            return Err(MacroRuntimeError::new(
                expr.span,
                "unsupported expression in macro body",
            ));
        }
    };
    Ok(CoreExpr {
        span: expr.span,
        kind,
    })
}

fn lower_stmt(stmt: &Stmt) -> Result<CoreStmt, MacroRuntimeError> {
    let kind = match stmt {
        Stmt::Let { pat, value, .. } => CoreStmtKind::Let {
            pat: pat.clone(),
            value: lower_expr(value)?,
        },
        Stmt::Expr(expr) => CoreStmtKind::Expr(lower_expr(expr)?),
        _ => {
            return Err(MacroRuntimeError::new(
                stmt.span(),
                "unsupported statement in macro body",
            ));
        }
    };
    Ok(CoreStmt {
        span: stmt.span(),
        kind,
    })
}

fn lower_array_entry(entry: &ArrayEntry) -> Result<CoreExpr, MacroRuntimeError> {
    match entry {
        ArrayEntry::Elem(expr) => lower_expr(expr),
        ArrayEntry::Spread(expr) => Err(MacroRuntimeError::new(
            expr.span,
            "unsupported array spread in macro body",
        )),
    }
}

fn lower_record_entry(entry: &RecordEntry) -> Result<(String, CoreExpr), MacroRuntimeError> {
    match entry {
        RecordEntry::Field(name, expr) => Ok((name.clone(), lower_expr(expr)?)),
        RecordEntry::Spread(expr) => Err(MacroRuntimeError::new(
            expr.span,
            "unsupported record spread in macro body",
        )),
    }
}

fn lower_callee(callee: &Expr) -> Result<CoreCallee, MacroRuntimeError> {
    match &callee.kind {
        ExprKind::Ident(name) => Ok(CoreCallee::Ident(name.clone())),
        ExprKind::FieldAccess {
            expr,
            field,
            field_span,
        } => Ok(CoreCallee::Method {
            receiver: Box::new(lower_expr(expr)?),
            name: field.clone(),
            span: *field_span,
        }),
        _ => Ok(CoreCallee::Expr(Box::new(lower_expr(callee)?))),
    }
}

fn lower_assign_target(target: &Expr) -> CoreAssignTarget {
    match &target.kind {
        ExprKind::Ident(name) => CoreAssignTarget::Ident(name.clone()),
        _ => CoreAssignTarget::Unsupported(target.span),
    }
}

fn lower_binary_op(op: &BinOp) -> Option<CoreBinaryOp> {
    match op {
        BinOp::Custom(op) if op == "==" => Some(CoreBinaryOp::Eq),
        BinOp::Custom(op) if op == "!=" => Some(CoreBinaryOp::NotEq),
        BinOp::Custom(op) if op == "&&" => Some(CoreBinaryOp::And),
        BinOp::Custom(op) if op == "||" => Some(CoreBinaryOp::Or),
        BinOp::Custom(op) if op == "+" => Some(CoreBinaryOp::Add),
        BinOp::Custom(op) if op == "-" => Some(CoreBinaryOp::Sub),
        BinOp::Custom(op) if op == "<" => Some(CoreBinaryOp::Lt),
        BinOp::Custom(op) if op == "<=" => Some(CoreBinaryOp::Le),
        BinOp::Custom(op) if op == ">" => Some(CoreBinaryOp::Gt),
        BinOp::Custom(op) if op == ">=" => Some(CoreBinaryOp::Ge),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lex::Lexer;
    use crate::parse::Parser;
    use crate::pipeline::parse_source;

    fn parse_expr(source: &str) -> Expr {
        let tokens = Lexer::new(source)
            .tokenize()
            .expect("expression should lex");
        Parser::new(&tokens)
            .parse_expr_fragment()
            .expect("expression should parse")
    }

    fn first_macro_body(source: &str) -> Expr {
        let program = parse_source(source).expect("source should parse");
        let Stmt::Macro(def) = &program.stmts[0] else {
            panic!("expected macro definition");
        };
        def.body.clone()
    }

    #[test]
    fn lowers_current_expression_surface_to_core_ir() {
        let body = first_macro_body(
            r#"
macro demo(input: Syntax) -> MacroResult(Syntax) {
  let xs = [1, 2];
  let pair = (xs[0], #{ name: "hern" });
  let count = 0;
  loop {
    break count;
  }
  match input {
    '{$name:ident} -> {
      if syntax_is_ident(input, "foo") {
        Ok('{ $name })
      } else {
        Ok('{ pair.0 })
      }
    },
    _ -> Ok('{ pair.1.name }),
  }
}
"#,
        );

        let lowered = lower_macro_body_to_core(&body).expect("current macro surface should lower");
        assert!(matches!(lowered.expr.kind, CoreExprKind::Block { .. }));
    }

    #[test]
    fn rejects_forms_outside_current_core_ir() {
        let array_spread = parse_expr("[..xs]");
        let err = lower_macro_body_to_core(&array_spread)
            .expect_err("array spread is not in the macro core IR yet");
        assert!(err.message.contains("unsupported array spread"));
    }
}
