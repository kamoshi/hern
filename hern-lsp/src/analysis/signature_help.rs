use super::hover::ty_to_display_string;
use super::state::{ServerState, cached_analysis};
use super::uri::uri_to_path;
use super::workspace::load_workspace_graphs;
use hern_core::ast::{Expr, ExprKind, Program, SourcePosition, SourceSpan, Stmt};
use hern_core::types::{ParamCapability, Ty};
use lsp_types::{
    ParameterInformation, ParameterLabel, Position, SignatureHelp, SignatureInformation, Uri,
};

pub(crate) fn signature_help(
    state: &ServerState,
    uri: Uri,
    position: Position,
) -> Option<SignatureHelp> {
    let path = uri_to_path(&uri)?;
    let fallback;
    let (graph, inference) = if let Some(analysis) = cached_analysis(state, &uri) {
        (&analysis.graph, &analysis.inference)
    } else {
        fallback = load_workspace_graphs(state, &uri)?;
        (&fallback.graph, &fallback.inference)
    };
    let (module_name, program) = graph.module_for_path(&path)?;
    let expr_types = inference.expr_types_for_module(module_name)?;
    let symbol_types = inference.symbol_types_for_module(module_name)?;
    let callable_capabilities = inference.callable_capabilities_for_module(module_name);
    let source_position = SourcePosition {
        line: position.line as usize + 1,
        col: position.character as usize + 1,
    };
    let call = innermost_call_at(program, source_position)?;
    let callee_ty = symbol_types
        .get(&call.callee.id)
        .or_else(|| expr_types.get(&call.callee.id))?;
    let Ty::Func(params, ret) = callee_ty else {
        return None;
    };

    let capabilities = callable_capabilities
        .and_then(|capabilities| capabilities.get(&call.callee.id))
        .map(|capabilities| capabilities.param_capabilities.as_slice())
        .unwrap_or(&[]);
    let param_labels = params
        .iter()
        .enumerate()
        .map(|(idx, ty)| {
            let text = ty_to_display_string(ty);
            if capabilities
                .get(idx)
                .is_some_and(|capability| matches!(capability, ParamCapability::MutPlace))
            {
                format!("mut {text}")
            } else {
                text
            }
        })
        .collect::<Vec<_>>();
    let label = format!(
        "fn({}) -> {}",
        param_labels.join(", "),
        ty_to_display_string(ret)
    );
    let parameters = param_labels
        .into_iter()
        .map(|label| ParameterInformation {
            label: ParameterLabel::Simple(label),
            documentation: None,
        })
        .collect::<Vec<_>>();

    Some(SignatureHelp {
        signatures: vec![SignatureInformation {
            label,
            documentation: None,
            parameters: Some(parameters),
            active_parameter: None,
        }],
        active_signature: Some(0),
        active_parameter: Some(active_parameter(call.args, source_position) as u32),
    })
}

struct CallSite<'a> {
    callee: &'a Expr,
    args: &'a [Expr],
    span: SourceSpan,
}

fn innermost_call_at(program: &Program, position: SourcePosition) -> Option<CallSite<'_>> {
    let mut best = None;
    for stmt in &program.stmts {
        find_call_in_stmt(stmt, position, &mut best);
    }
    best
}

fn find_call_in_stmt<'a>(
    stmt: &'a Stmt,
    position: SourcePosition,
    best: &mut Option<CallSite<'a>>,
) {
    match stmt {
        Stmt::Let { value, .. } => find_call_in_expr(value, position, best),
        Stmt::Fn { body, .. } | Stmt::Op { body, .. } => find_call_in_expr(body, position, best),
        Stmt::Impl(impl_def) => {
            for method in &impl_def.methods {
                find_call_in_expr(&method.body, position, best);
            }
        }
        Stmt::InherentImpl(impl_def) => {
            for method in &impl_def.methods {
                find_call_in_expr(&method.body, position, best);
            }
        }
        Stmt::Expr(expr) => find_call_in_expr(expr, position, best),
        Stmt::Trait(_) | Stmt::Type(_) | Stmt::TypeAlias { .. } | Stmt::Extern { .. } => {}
    }
}

fn find_call_in_expr<'a>(
    expr: &'a Expr,
    position: SourcePosition,
    best: &mut Option<CallSite<'a>>,
) {
    if !contains(expr.span, position) {
        return;
    }
    match &expr.kind {
        ExprKind::Call { callee, args, .. } => {
            if call_argument_area_contains(expr.span, callee.span, position) {
                let candidate = CallSite {
                    callee,
                    args,
                    span: expr.span,
                };
                if best
                    .as_ref()
                    .is_none_or(|current| span_len(candidate.span) < span_len(current.span))
                {
                    *best = Some(candidate);
                }
            }
            find_call_in_expr(callee, position, best);
            for arg in args {
                find_call_in_expr(arg, position, best);
            }
        }
        ExprKind::Not(inner)
        | ExprKind::Loop(inner)
        | ExprKind::Break(Some(inner))
        | ExprKind::Return(Some(inner))
        | ExprKind::FieldAccess { expr: inner, .. } => find_call_in_expr(inner, position, best),
        ExprKind::Assign { target, value } => {
            find_call_in_expr(target, position, best);
            find_call_in_expr(value, position, best);
        }
        ExprKind::Binary { lhs, rhs, .. } => {
            find_call_in_expr(lhs, position, best);
            find_call_in_expr(rhs, position, best);
        }
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
        } => {
            find_call_in_expr(cond, position, best);
            find_call_in_expr(then_branch, position, best);
            find_call_in_expr(else_branch, position, best);
        }
        ExprKind::Match { scrutinee, arms } => {
            find_call_in_expr(scrutinee, position, best);
            for (_, body) in arms {
                find_call_in_expr(body, position, best);
            }
        }
        ExprKind::Block { stmts, final_expr } => {
            for stmt in stmts {
                find_call_in_stmt(stmt, position, best);
            }
            if let Some(expr) = final_expr {
                find_call_in_expr(expr, position, best);
            }
        }
        ExprKind::Tuple(items) => {
            for item in items {
                find_call_in_expr(item, position, best);
            }
        }
        ExprKind::Array(entries) => {
            for entry in entries {
                find_call_in_expr(entry.expr(), position, best);
            }
        }
        ExprKind::Record(entries) => {
            for entry in entries {
                find_call_in_expr(entry.expr(), position, best);
            }
        }
        ExprKind::Lambda { body, .. } => find_call_in_expr(body, position, best),
        ExprKind::For { iterable, body, .. } => {
            find_call_in_expr(iterable, position, best);
            find_call_in_expr(body, position, best);
        }
        ExprKind::Number(_)
        | ExprKind::StringLit(_)
        | ExprKind::Bool(_)
        | ExprKind::Ident(_)
        | ExprKind::Import(_)
        | ExprKind::Break(None)
        | ExprKind::Continue
        | ExprKind::Return(None)
        | ExprKind::Unit => {}
    }
}

fn call_argument_area_contains(
    call_span: SourceSpan,
    callee_span: SourceSpan,
    position: SourcePosition,
) -> bool {
    contains(call_span, position)
        && (position.line, position.col) >= (callee_span.end_line, callee_span.end_col)
}

fn active_parameter(args: &[Expr], position: SourcePosition) -> usize {
    if args.is_empty() {
        return 0;
    }
    for (idx, arg) in args.iter().enumerate() {
        if (position.line, position.col) <= (arg.span.end_line, arg.span.end_col) {
            return idx;
        }
    }
    args.len().saturating_sub(1)
}

fn contains(span: SourceSpan, pos: SourcePosition) -> bool {
    (pos.line, pos.col) >= (span.start_line, span.start_col)
        && (pos.line, pos.col) < (span.end_line, span.end_col)
}

fn span_len(span: SourceSpan) -> usize {
    (span.end_line.saturating_sub(span.start_line) * 100_000)
        + span.end_col.saturating_sub(span.start_col)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::analysis::tests::{ImportFixture, import_fixture};

    fn signature_labels(help: SignatureHelp) -> (String, Vec<String>, u32) {
        let signature = help
            .signatures
            .into_iter()
            .next()
            .expect("signature help should include a signature");
        let params = signature
            .parameters
            .unwrap_or_default()
            .into_iter()
            .map(|param| match param.label {
                ParameterLabel::Simple(label) => label,
                ParameterLabel::LabelOffsets(_) => panic!("unexpected offset label"),
            })
            .collect();
        (
            label_without_docs(signature.label),
            params,
            help.active_parameter.unwrap_or(0),
        )
    }

    fn label_without_docs(label: String) -> String {
        label
    }

    #[test]
    fn signature_help_for_top_level_function_call() {
        let project = crate::analysis::tests::TestProject::new("signature-help");
        let source = "fn add(x: f64, y: f64) -> f64 { x + y }\nadd(1, 2)\n";
        let (state, uri) = project.open("main.hern", source);

        let help = signature_help(&state, uri, Position::new(1, 5)).expect("signature help");
        let (label, params, active) = signature_labels(help);

        assert_eq!(label, "fn(f64, f64) -> f64");
        assert_eq!(params, vec!["f64", "f64"]);
        assert_eq!(active, 0);
    }

    #[test]
    fn signature_help_active_parameter_after_comma() {
        let project = crate::analysis::tests::TestProject::new("signature-active-param");
        let source = "fn add(x: f64, y: f64) -> f64 { x + y }\nadd(1, 2)\n";
        let (state, uri) = project.open("main.hern", source);

        let help = signature_help(&state, uri, Position::new(1, 8)).expect("signature help");

        assert_eq!(help.active_parameter, Some(1));
    }

    #[test]
    fn signature_help_chooses_innermost_call() {
        let project = crate::analysis::tests::TestProject::new("signature-innermost");
        let source = "fn add(x: f64, y: f64) -> f64 { x + y }\nadd(add(1, 2), 3)\n";
        let (state, uri) = project.open("main.hern", source);

        let help = signature_help(&state, uri, Position::new(1, 9)).expect("signature help");

        assert_eq!(help.active_parameter, Some(0));
    }

    #[test]
    fn signature_help_for_imported_member_function() {
        let ImportFixture {
            state, entry_uri, ..
        } = import_fixture(
            "signature-imported",
            "let dep = import \"dep\";\ndep.add(1, 2)\n",
            "fn add(x: f64, y: f64) -> f64 { x + y }\n#{ add: add }\n",
        );

        let help = signature_help(&state, entry_uri, Position::new(1, 9)).expect("signature help");
        let (label, _, active) = signature_labels(help);

        assert_eq!(label, "fn(f64, f64) -> f64");
        assert_eq!(active, 0);
    }

    #[test]
    fn signature_help_shows_mutable_place_parameter() {
        let project = crate::analysis::tests::TestProject::new("signature-mut-param");
        let source = concat!(
            "fn bump(mut r: #{ x: f64 }) { r.x = r.x + 1; }\n",
            "let mut r = #{ x: 1 };\n",
            "bump(r)\n",
        );
        let (state, uri) = project.open("main.hern", source);

        let help = signature_help(&state, uri, Position::new(2, 5)).expect("signature help");
        let (label, params, active) = signature_labels(help);

        assert_eq!(label, "fn(mut #{ x: f64 }) -> ()");
        assert_eq!(params, vec!["mut #{ x: f64 }"]);
        assert_eq!(active, 0);
    }

    #[test]
    fn signature_help_returns_none_outside_call_context() {
        let project = crate::analysis::tests::TestProject::new("signature-none");
        let source = "fn add(x: f64, y: f64) -> f64 { x + y }\nadd\n";
        let (state, uri) = project.open("main.hern", source);

        assert!(signature_help(&state, uri, Position::new(1, 1)).is_none());
    }
}
