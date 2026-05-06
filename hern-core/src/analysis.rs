use crate::ast::{Expr, ExprKind, NodeId, Program, SourcePosition, SourceSpan, Stmt};
use crate::pipeline::{
    infer_program, infer_program_with_seed, parse_source, reassociate_standalone,
    reassociate_with_program,
};
use crate::types::Ty;
use crate::types::infer::{InferenceResult, TypeEnv, VariantEnv};
use std::collections::HashMap;
use std::fmt;
use std::path::PathBuf;

const PRELUDE: &str = include_str!("../../std/prelude.hern");
// Used only to sort spans by approximate source size; source lines should never approach this width.
const MAX_REASONABLE_SOURCE_COLUMNS: usize = 100_000;

#[derive(Debug, Clone)]
pub struct HoverInfo {
    pub node_id: NodeId,
    pub span: SourceSpan,
    pub ty: Ty,
}

#[derive(Debug, Clone)]
pub struct PreludeAnalysis {
    pub program: Program,
    pub env: TypeEnv,
    pub variant_env: VariantEnv,
}

#[derive(Debug, Clone)]
pub struct Analysis {
    pub program: Program,
    pub inference: InferenceResult,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DiagnosticSeverity {
    Error,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DiagnosticSource {
    Path(PathBuf),
    Module(String),
    Prelude,
}

#[derive(Debug, Clone)]
pub struct CompilerDiagnostic {
    pub source: Option<DiagnosticSource>,
    pub span: Option<SourceSpan>,
    pub severity: DiagnosticSeverity,
    pub message: String,
}

impl CompilerDiagnostic {
    pub fn error(span: Option<SourceSpan>, message: impl Into<String>) -> Self {
        Self {
            source: None,
            span,
            severity: DiagnosticSeverity::Error,
            message: message.into(),
        }
    }

    pub fn error_in(
        source: DiagnosticSource,
        span: Option<SourceSpan>,
        message: impl Into<String>,
    ) -> Self {
        Self {
            source: Some(source),
            span,
            severity: DiagnosticSeverity::Error,
            message: message.into(),
        }
    }

    pub fn with_source(mut self, source: DiagnosticSource) -> Self {
        self.source = Some(source);
        self
    }

    pub fn with_source_if_absent(mut self, source: DiagnosticSource) -> Self {
        if self.source.is_none() {
            self.source = Some(source);
        }
        self
    }

    pub fn with_span_if_absent(mut self, span: SourceSpan) -> Self {
        if self.span.is_none() {
            self.span = Some(span);
        }
        self
    }
}

impl fmt::Display for CompilerDiagnostic {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.source {
            Some(DiagnosticSource::Path(path)) => write!(f, "{}: {}", path.display(), self.message),
            Some(DiagnosticSource::Module(module)) => write!(f, "{}: {}", module, self.message),
            Some(DiagnosticSource::Prelude) => write!(f, "<prelude>: {}", self.message),
            None => write!(f, "{}", self.message),
        }
    }
}

impl std::error::Error for CompilerDiagnostic {}

pub fn analyze_prelude() -> Result<PreludeAnalysis, CompilerDiagnostic> {
    let mut program = parse_source(PRELUDE)?;
    reassociate_standalone(&mut program);

    let inference = infer_program(&mut program)?;
    let env = inference.env;
    let variant_env = inference.variant_env;

    Ok(PreludeAnalysis {
        program,
        env,
        variant_env,
    })
}

pub fn analyze_source(
    source: &str,
    prelude: &PreludeAnalysis,
) -> Result<Analysis, CompilerDiagnostic> {
    let mut program = parse_source(source)?;
    reassociate_with_program(&mut program, &prelude.program);

    let inference =
        infer_program_with_seed(&mut program, &prelude.program.stmts, Some(&prelude.env))?;

    Ok(Analysis { program, inference })
}

pub fn hover_at(
    program: &Program,
    expr_types: &HashMap<NodeId, Ty>,
    symbol_types: &HashMap<NodeId, Ty>,
    pos: SourcePosition,
) -> Option<HoverInfo> {
    let mut best = None;
    for stmt in &program.stmts {
        find_hover_in_stmt(stmt, expr_types, symbol_types, pos, &mut best);
    }
    best
}

fn find_hover_in_stmt(
    stmt: &Stmt,
    expr_types: &HashMap<NodeId, Ty>,
    symbol_types: &HashMap<NodeId, Ty>,
    pos: SourcePosition,
    best: &mut Option<HoverInfo>,
) {
    match stmt {
        Stmt::Let { value, .. } | Stmt::Expr(value) => {
            find_hover_in_expr(value, expr_types, symbol_types, pos, best)
        }
        Stmt::Fn { body, .. } | Stmt::Op { body, .. } => {
            find_hover_in_expr(body, expr_types, symbol_types, pos, best)
        }
        Stmt::Impl(id) => {
            for method in &id.methods {
                find_hover_in_expr(&method.body, expr_types, symbol_types, pos, best);
            }
        }
        Stmt::InherentImpl(id) => {
            for method in &id.methods {
                find_hover_in_expr(&method.body, expr_types, symbol_types, pos, best);
            }
        }
        Stmt::Type(_) | Stmt::TypeAlias { .. } | Stmt::Trait(_) | Stmt::Extern { .. } => {}
    }
}

fn find_hover_in_expr(
    expr: &Expr,
    expr_types: &HashMap<NodeId, Ty>,
    symbol_types: &HashMap<NodeId, Ty>,
    pos: SourcePosition,
    best: &mut Option<HoverInfo>,
) {
    if !contains(expr.span, pos) {
        return;
    }

    let ty = symbol_types
        .get(&expr.id)
        .or_else(|| expr_types.get(&expr.id));
    if let Some(ty) = ty
        && best
            .as_ref()
            .is_none_or(|current| span_len(expr.span) <= span_len(current.span))
    {
        *best = Some(HoverInfo {
            node_id: expr.id,
            span: expr.span,
            ty: ty.clone(),
        });
    }

    match &expr.kind {
        ExprKind::Not(e)
        | ExprKind::Loop(e)
        | ExprKind::Break(Some(e))
        | ExprKind::Return(Some(e))
        | ExprKind::FieldAccess { expr: e, .. }
        | ExprKind::Lambda { body: e, .. } => {
            find_hover_in_expr(e, expr_types, symbol_types, pos, best)
        }
        ExprKind::Assign { target, value } => {
            find_hover_in_expr(target, expr_types, symbol_types, pos, best);
            find_hover_in_expr(value, expr_types, symbol_types, pos, best);
        }
        ExprKind::Binary {
            lhs, op_span, rhs, ..
        } => {
            find_hover_in_expr(lhs, expr_types, symbol_types, pos, best);
            find_hover_in_expr(rhs, expr_types, symbol_types, pos, best);
            if contains(*op_span, pos) {
                let lhs_ty = symbol_types
                    .get(&lhs.id)
                    .or_else(|| expr_types.get(&lhs.id));
                let rhs_ty = symbol_types
                    .get(&rhs.id)
                    .or_else(|| expr_types.get(&rhs.id));
                let result_ty = expr_types
                    .get(&expr.id)
                    .or_else(|| symbol_types.get(&expr.id));
                if let (Some(l), Some(r), Some(res)) = (lhs_ty, rhs_ty, result_ty) {
                    let op_ty = Ty::Func(
                        crate::types::value_func_params(vec![l.clone(), r.clone()]),
                        crate::types::value_func_return(res.clone()),
                    );
                    if best
                        .as_ref()
                        .is_none_or(|cur| span_len(*op_span) <= span_len(cur.span))
                    {
                        *best = Some(HoverInfo {
                            node_id: expr.id,
                            span: *op_span,
                            ty: op_ty,
                        });
                    }
                }
            }
        }
        ExprKind::Call { callee, args, .. } => {
            find_hover_in_expr(callee, expr_types, symbol_types, pos, best);
            for arg in args {
                find_hover_in_expr(arg, expr_types, symbol_types, pos, best);
            }
        }
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
        } => {
            find_hover_in_expr(cond, expr_types, symbol_types, pos, best);
            find_hover_in_expr(then_branch, expr_types, symbol_types, pos, best);
            find_hover_in_expr(else_branch, expr_types, symbol_types, pos, best);
        }
        ExprKind::Match { scrutinee, arms } => {
            find_hover_in_expr(scrutinee, expr_types, symbol_types, pos, best);
            for (_, body) in arms {
                find_hover_in_expr(body, expr_types, symbol_types, pos, best);
            }
        }
        ExprKind::Block { stmts, final_expr } => {
            for stmt in stmts {
                find_hover_in_stmt(stmt, expr_types, symbol_types, pos, best);
            }
            if let Some(expr) = final_expr {
                find_hover_in_expr(expr, expr_types, symbol_types, pos, best);
            }
        }
        ExprKind::Tuple(items) => {
            for item in items {
                find_hover_in_expr(item, expr_types, symbol_types, pos, best);
            }
        }
        ExprKind::Array(entries) => {
            for entry in entries {
                find_hover_in_expr(entry.expr(), expr_types, symbol_types, pos, best);
            }
        }
        ExprKind::Record(entries) => {
            for entry in entries {
                find_hover_in_expr(entry.expr(), expr_types, symbol_types, pos, best);
            }
        }
        ExprKind::For { iterable, body, .. } => {
            find_hover_in_expr(iterable, expr_types, symbol_types, pos, best);
            find_hover_in_expr(body, expr_types, symbol_types, pos, best);
        }
        ExprKind::Break(None)
        | ExprKind::Return(None)
        | ExprKind::Continue
        | ExprKind::Number(_)
        | ExprKind::StringLit(_)
        | ExprKind::Bool(_)
        | ExprKind::Ident(_)
        | ExprKind::Import(_)
        | ExprKind::Unit => {}
    }
}

fn contains(span: SourceSpan, pos: SourcePosition) -> bool {
    if span.start_line == 0 {
        return false;
    }
    (pos.line, pos.col) >= (span.start_line, span.start_col)
        && (pos.line, pos.col) < (span.end_line, span.end_col)
}

fn span_len(span: SourceSpan) -> usize {
    (span.end_line.saturating_sub(span.start_line) * MAX_REASONABLE_SOURCE_COLUMNS)
        + span.end_col.saturating_sub(span.start_col)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn find_method_callee(program: &Program, method_name: &str) -> Option<(NodeId, SourceSpan)> {
        fn find_in_expr(expr: &Expr, method_name: &str) -> Option<(NodeId, SourceSpan)> {
            match &expr.kind {
                ExprKind::Call { callee, args, .. } => {
                    if let ExprKind::FieldAccess {
                        field, field_span, ..
                    } = &callee.kind
                        && field == method_name
                    {
                        return Some((callee.id, *field_span));
                    }
                    find_in_expr(callee, method_name)
                        .or_else(|| args.iter().find_map(|arg| find_in_expr(arg, method_name)))
                }
                ExprKind::FieldAccess { expr, .. }
                | ExprKind::Not(expr)
                | ExprKind::Loop(expr)
                | ExprKind::Break(Some(expr))
                | ExprKind::Return(Some(expr)) => find_in_expr(expr, method_name),
                ExprKind::Assign { target, value }
                | ExprKind::Binary {
                    lhs: target,
                    rhs: value,
                    ..
                } => find_in_expr(target, method_name).or_else(|| find_in_expr(value, method_name)),
                ExprKind::If {
                    cond,
                    then_branch,
                    else_branch,
                } => find_in_expr(cond, method_name)
                    .or_else(|| find_in_expr(then_branch, method_name))
                    .or_else(|| find_in_expr(else_branch, method_name)),
                ExprKind::Match { scrutinee, arms } => find_in_expr(scrutinee, method_name)
                    .or_else(|| {
                        arms.iter()
                            .find_map(|(_, body)| find_in_expr(body, method_name))
                    }),
                ExprKind::Block { stmts, final_expr } => stmts
                    .iter()
                    .find_map(|stmt| find_in_stmt(stmt, method_name))
                    .or_else(|| {
                        final_expr
                            .as_deref()
                            .and_then(|expr| find_in_expr(expr, method_name))
                    }),
                ExprKind::Tuple(items) => items
                    .iter()
                    .find_map(|item| find_in_expr(item, method_name)),
                ExprKind::Array(entries) => entries
                    .iter()
                    .find_map(|entry| find_in_expr(entry.expr(), method_name)),
                ExprKind::Record(entries) => entries
                    .iter()
                    .find_map(|entry| find_in_expr(entry.expr(), method_name)),
                ExprKind::Lambda { body, .. } | ExprKind::For { body, .. } => {
                    find_in_expr(body, method_name)
                }
                ExprKind::Number(_)
                | ExprKind::StringLit(_)
                | ExprKind::Bool(_)
                | ExprKind::Ident(_)
                | ExprKind::Import(_)
                | ExprKind::Unit
                | ExprKind::Break(None)
                | ExprKind::Continue
                | ExprKind::Return(None) => None,
            }
        }

        fn find_in_stmt(stmt: &Stmt, method_name: &str) -> Option<(NodeId, SourceSpan)> {
            match stmt {
                Stmt::Let { value, .. } | Stmt::Expr(value) => find_in_expr(value, method_name),
                Stmt::Fn { body, .. } | Stmt::Op { body, .. } => find_in_expr(body, method_name),
                Stmt::Impl(id) => id
                    .methods
                    .iter()
                    .find_map(|method| find_in_expr(&method.body, method_name)),
                Stmt::InherentImpl(id) => id
                    .methods
                    .iter()
                    .find_map(|method| find_in_expr(&method.body, method_name)),
                Stmt::Type(_) | Stmt::TypeAlias { .. } | Stmt::Trait(_) | Stmt::Extern { .. } => {
                    None
                }
            }
        }

        program
            .stmts
            .iter()
            .find_map(|stmt| find_in_stmt(stmt, method_name))
    }

    #[test]
    fn type_error_in_expression_has_span() {
        let prelude = analyze_prelude().expect("prelude should analyze");
        let err = analyze_source("let x: bool = 1;", &prelude)
            .expect_err("annotated let should reject mismatched value type");

        let span = err.span.expect("type error should carry a source span");
        assert_eq!(span.start_line, 1);
        assert!(span.start_col > 0);
        assert!(span.end_col >= span.start_col);
    }

    #[test]
    fn declaration_type_error_has_span() {
        let prelude = analyze_prelude().expect("prelude should analyze");
        let err = analyze_source("extern value: MissingType = \"value\";", &prelude)
            .expect_err("unknown extern type should be rejected");

        let span = err.span.expect("declaration error should carry a span");
        assert_eq!(span.start_line, 1);
        assert_eq!(span.start_col, 1);
        assert!(span.end_col > span.start_col);
    }

    #[test]
    fn contains_treats_span_end_as_exclusive() {
        let span = SourceSpan {
            start_line: 1,
            start_col: 1,
            end_line: 1,
            end_col: 6,
        };

        assert!(contains(span, SourcePosition { line: 1, col: 5 }));
        assert!(!contains(span, SourcePosition { line: 1, col: 6 }));
    }

    #[test]
    fn hover_reaches_resolved_inherent_method_name() {
        let prelude = analyze_prelude().expect("prelude should analyze");
        let analysis = analyze_source(
            r#"
impl Option('a) {
  fn present(self) {
    match self {
      Some(_) -> true,
      None -> false,
    }
  }
}

let wrapped = Some(1);
let is_present = wrapped.present();
"#,
            &prelude,
        )
        .expect("source should analyze");

        let (callee_id, method_span) = find_method_callee(&analysis.program, "present")
            .expect("method call callee should be present");

        assert!(analysis.inference.symbol_types.contains_key(&callee_id));

        let hover = hover_at(
            &analysis.program,
            &analysis.inference.expr_types,
            &analysis.inference.symbol_types,
            SourcePosition {
                line: method_span.start_line,
                col: method_span.start_col,
            },
        )
        .expect("method name should have hover info");

        assert_eq!(hover.node_id, callee_id);
        assert!(matches!(hover.ty, Ty::Func(_, _)));
    }
}
