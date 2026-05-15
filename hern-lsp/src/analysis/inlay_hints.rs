use super::hover::{ty_to_display_string, ty_to_display_string_in_scheme};
use super::snapshot::{SnapshotMode, analysis_snapshot};
use super::uri::source_span_to_range;
use hern_core::ast::{Expr, ExprKind, Param, Pattern, SourceSpan, Stmt};
use hern_core::types::{Scheme, Ty};
use lsp_types::{InlayHint, InlayHintKind, InlayHintLabel, Position, Range, Uri};
use std::collections::HashMap;

pub(crate) fn inlay_hints(
    state: &super::state::ServerState,
    uri: Uri,
    range: Range,
) -> Option<Vec<InlayHint>> {
    let snapshot = analysis_snapshot(state, &uri, SnapshotMode::RequireTyped)?;
    let inference = snapshot.inference()?;
    let (module_name, program) = snapshot.module()?;
    let binding_types = inference.binding_types_for_module(module_name)?;
    let definition_schemes = inference.definition_schemes_for_module(module_name);

    let mut hints = Vec::new();
    for stmt in &program.stmts {
        collect_stmt_hints(stmt, range, binding_types, definition_schemes, &mut hints);
    }
    hints.sort_by_key(|hint| (hint.position.line, hint.position.character));
    Some(hints)
}

fn collect_stmt_hints(
    stmt: &Stmt,
    range: Range,
    binding_types: &HashMap<SourceSpan, Ty>,
    definition_schemes: Option<&HashMap<SourceSpan, Scheme>>,
    hints: &mut Vec<InlayHint>,
) {
    match stmt {
        Stmt::Let {
            pat,
            ty: None,
            value,
            ..
        } => {
            collect_pattern_type_hints(pat, range, binding_types, hints);
            collect_expr_hints(value, range, binding_types, definition_schemes, hints);
        }
        Stmt::Let { value, .. } | Stmt::Expr(value) => {
            collect_expr_hints(value, range, binding_types, definition_schemes, hints);
        }
        Stmt::Fn {
            name_span,
            params,
            ret_type,
            body,
            ..
        }
        | Stmt::Op {
            name_span,
            params,
            ret_type,
            body,
            ..
        } => {
            let scheme = definition_schemes.and_then(|schemes| schemes.get(name_span));
            collect_callable_hints(
                params,
                ret_type.is_none(),
                body,
                scheme,
                range,
                binding_types,
                hints,
            );
            collect_expr_hints(body, range, binding_types, definition_schemes, hints);
        }
        Stmt::Impl(impl_def) => {
            for method in &impl_def.methods {
                let scheme = definition_schemes.and_then(|schemes| schemes.get(&method.name_span));
                collect_callable_hints(
                    &method.params,
                    method.ret_type.is_none(),
                    &method.body,
                    scheme,
                    range,
                    binding_types,
                    hints,
                );
                collect_expr_hints(
                    &method.body,
                    range,
                    binding_types,
                    definition_schemes,
                    hints,
                );
            }
        }
        Stmt::InherentImpl(impl_def) => {
            for method in &impl_def.methods {
                let scheme = definition_schemes.and_then(|schemes| schemes.get(&method.name_span));
                collect_callable_hints(
                    &method.params,
                    method.ret_type.is_none(),
                    &method.body,
                    scheme,
                    range,
                    binding_types,
                    hints,
                );
                collect_expr_hints(
                    &method.body,
                    range,
                    binding_types,
                    definition_schemes,
                    hints,
                );
            }
        }
        Stmt::Trait(_) | Stmt::Type(_) | Stmt::TypeAlias { .. } | Stmt::Extern { .. } => {}
    }
}

fn collect_callable_hints(
    params: &[Param],
    return_is_inferred: bool,
    body: &Expr,
    scheme: Option<&Scheme>,
    range: Range,
    binding_types: &HashMap<SourceSpan, Ty>,
    hints: &mut Vec<InlayHint>,
) {
    for param in params {
        if param.ty.is_none() {
            let scheme_text = scheme
                .and_then(|scheme| {
                    callable_param_type(scheme, params, param).map(|ty| (scheme, ty))
                })
                .map(|(scheme, ty)| ty_to_display_string_in_scheme(ty, scheme));
            collect_pattern_type_hints_with_type(
                &param.pat,
                scheme_text.as_deref(),
                range,
                binding_types,
                hints,
            );
        }
    }
    if return_is_inferred {
        collect_return_type_hint(body, scheme, range, hints);
    }
}

fn callable_param_type<'a>(scheme: &'a Scheme, params: &[Param], param: &Param) -> Option<&'a Ty> {
    let index = params
        .iter()
        .position(|candidate| std::ptr::eq(candidate, param))?;
    match &scheme.ty {
        Ty::Func(param_tys, _) => param_tys.get(index).map(|param| &param.ty),
        _ => None,
    }
}

fn collect_return_type_hint(
    body: &Expr,
    scheme: Option<&Scheme>,
    range: Range,
    hints: &mut Vec<InlayHint>,
) {
    let Some(Ty::Func(_, ret)) = scheme.map(|scheme| &scheme.ty) else {
        return;
    };
    let body_range = source_span_to_range(body.span);
    if !ranges_intersect(body_range, range) {
        return;
    }
    let text = scheme
        .map(|scheme| ty_to_display_string_in_scheme(&ret.ty, scheme))
        .unwrap_or_else(|| ty_to_display_string(&ret.ty));
    if !text.contains('\n') {
        hints.push(InlayHint {
            position: body_range.start,
            label: InlayHintLabel::String(format!(" -> {text}")),
            kind: Some(InlayHintKind::TYPE),
            text_edits: None,
            tooltip: None,
            padding_left: None,
            padding_right: None,
            data: None,
        });
    }
}

fn collect_pattern_type_hints(
    pat: &Pattern,
    range: Range,
    binding_types: &HashMap<SourceSpan, Ty>,
    hints: &mut Vec<InlayHint>,
) {
    collect_pattern_type_hints_with_type(pat, None, range, binding_types, hints);
}

fn collect_pattern_type_hints_with_type(
    pat: &Pattern,
    explicit_text: Option<&str>,
    range: Range,
    binding_types: &HashMap<SourceSpan, Ty>,
    hints: &mut Vec<InlayHint>,
) {
    if let Pattern::Variable(_, span) = pat
        && ranges_intersect(source_span_to_range(*span), range)
    {
        let text = explicit_text
            .map(ToOwned::to_owned)
            .or_else(|| binding_types.get(span).map(ty_to_display_string));
        let Some(text) = text else {
            return;
        };
        push_type_hint(source_span_to_range(*span).end, text, hints);
    }
    match pat {
        Pattern::Constructor { binding, .. } => {
            if let Some(binding) = binding {
                collect_pattern_type_hints(binding, range, binding_types, hints);
            }
        }
        Pattern::List { elements, rest } => {
            for element in elements {
                collect_pattern_type_hints(element, range, binding_types, hints);
            }
            collect_rest_pattern_type_hint(rest, range, binding_types, hints);
        }
        Pattern::Tuple(elements) => {
            for element in elements {
                collect_pattern_type_hints(element, range, binding_types, hints);
            }
        }
        Pattern::Record { fields, rest } => {
            for (_, binding_name, span) in fields {
                if binding_name != "_"
                    && ranges_intersect(source_span_to_range(*span), range)
                    && let Some(ty) = binding_types.get(span)
                {
                    push_type_hint(
                        source_span_to_range(*span).end,
                        ty_to_display_string(ty),
                        hints,
                    );
                }
            }
            collect_rest_pattern_type_hint(rest, range, binding_types, hints);
        }
        Pattern::Variable(_, _) | Pattern::Wildcard | Pattern::StringLit(_) => {}
    }
}

fn collect_rest_pattern_type_hint(
    rest: &hern_core::ast::RestPat,
    range: Range,
    binding_types: &HashMap<SourceSpan, Ty>,
    hints: &mut Vec<InlayHint>,
) {
    if let Some(Some((_, span))) = rest
        && ranges_intersect(source_span_to_range(*span), range)
        && let Some(ty) = binding_types.get(span)
    {
        push_type_hint(
            source_span_to_range(*span).end,
            ty_to_display_string(ty),
            hints,
        );
    }
}

fn push_type_hint(position: Position, text: String, hints: &mut Vec<InlayHint>) {
    if !text.contains('\n') {
        hints.push(InlayHint {
            position,
            label: InlayHintLabel::String(format!(": {}", text)),
            kind: Some(InlayHintKind::TYPE),
            text_edits: None,
            tooltip: None,
            padding_left: None,
            padding_right: None,
            data: None,
        });
    }
}

fn collect_expr_hints(
    expr: &Expr,
    range: Range,
    binding_types: &HashMap<SourceSpan, Ty>,
    definition_schemes: Option<&HashMap<SourceSpan, Scheme>>,
    hints: &mut Vec<InlayHint>,
) {
    match &expr.kind {
        ExprKind::Block { stmts, final_expr } => {
            for stmt in stmts {
                collect_stmt_hints(stmt, range, binding_types, definition_schemes, hints);
            }
            if let Some(expr) = final_expr {
                collect_expr_hints(expr, range, binding_types, definition_schemes, hints);
            }
        }
        ExprKind::Grouped(inner)
        | ExprKind::Not(inner)
        | ExprKind::Loop(inner)
        | ExprKind::Break(Some(inner))
        | ExprKind::Return(Some(inner))
        | ExprKind::FieldAccess { expr: inner, .. } => {
            collect_expr_hints(inner, range, binding_types, definition_schemes, hints);
        }
        ExprKind::Neg { operand, .. } => {
            collect_expr_hints(operand, range, binding_types, definition_schemes, hints);
        }
        ExprKind::Lambda { params, body, .. } => {
            for param in params {
                if param.ty.is_none() {
                    collect_pattern_type_hints(&param.pat, range, binding_types, hints);
                }
            }
            collect_expr_hints(body, range, binding_types, definition_schemes, hints);
        }
        ExprKind::Assign { target, value } => {
            collect_expr_hints(target, range, binding_types, definition_schemes, hints);
            collect_expr_hints(value, range, binding_types, definition_schemes, hints);
        }
        ExprKind::Binary { lhs, rhs, .. } => {
            collect_expr_hints(lhs, range, binding_types, definition_schemes, hints);
            collect_expr_hints(rhs, range, binding_types, definition_schemes, hints);
        }
        ExprKind::Range { start, end, .. } => {
            if let Some(start) = start {
                collect_expr_hints(start, range, binding_types, definition_schemes, hints);
            }
            if let Some(end) = end {
                collect_expr_hints(end, range, binding_types, definition_schemes, hints);
            }
        }
        ExprKind::Call { callee, args, .. } => {
            collect_expr_hints(callee, range, binding_types, definition_schemes, hints);
            for arg in args {
                collect_expr_hints(arg, range, binding_types, definition_schemes, hints);
            }
        }
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
        } => {
            collect_expr_hints(cond, range, binding_types, definition_schemes, hints);
            collect_expr_hints(then_branch, range, binding_types, definition_schemes, hints);
            collect_expr_hints(else_branch, range, binding_types, definition_schemes, hints);
        }
        ExprKind::Match { scrutinee, arms } => {
            collect_expr_hints(scrutinee, range, binding_types, definition_schemes, hints);
            for (_, body) in arms {
                collect_expr_hints(body, range, binding_types, definition_schemes, hints);
            }
        }
        ExprKind::Tuple(items) => {
            for item in items {
                collect_expr_hints(item, range, binding_types, definition_schemes, hints);
            }
        }
        ExprKind::Array(entries) => {
            for entry in entries {
                collect_expr_hints(
                    entry.expr(),
                    range,
                    binding_types,
                    definition_schemes,
                    hints,
                );
            }
        }
        ExprKind::Record(entries) => {
            for entry in entries {
                collect_expr_hints(
                    entry.expr(),
                    range,
                    binding_types,
                    definition_schemes,
                    hints,
                );
            }
        }
        ExprKind::For { iterable, body, .. } => {
            collect_expr_hints(iterable, range, binding_types, definition_schemes, hints);
            collect_expr_hints(body, range, binding_types, definition_schemes, hints);
        }
        ExprKind::Index { receiver, key, .. } => {
            collect_expr_hints(receiver, range, binding_types, definition_schemes, hints);
            collect_expr_hints(key, range, binding_types, definition_schemes, hints);
        }
        ExprKind::AssociatedAccess { .. }
        | ExprKind::Number(_)
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

fn ranges_intersect(lhs: Range, rhs: Range) -> bool {
    position_le(lhs.start, rhs.end) && position_le(rhs.start, lhs.end)
}

fn position_le(lhs: Position, rhs: Position) -> bool {
    (lhs.line, lhs.character) <= (rhs.line, rhs.character)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::analysis::tests::TestProject;

    #[test]
    fn inlay_hints_show_simple_let_type() {
        let project = TestProject::new("inlay-simple-let");
        let source = "let value = 1;\nvalue\n";
        let (state, uri) = project.open("main.hern", source);

        let hints = inlay_hints(
            &state,
            uri,
            Range::new(Position::new(0, 0), Position::new(2, 0)),
        )
        .expect("inlay hints should be available");

        assert_eq!(hints.len(), 1);
        assert_eq!(hints[0].position, Position::new(0, 9));
        assert!(matches!(&hints[0].label, InlayHintLabel::String(text) if text == ": int"));
    }

    #[test]
    fn inlay_hints_skip_explicit_let_type() {
        let project = TestProject::new("inlay-explicit-let");
        let source = "let value: int = 1;\nvalue\n";
        let (state, uri) = project.open("main.hern", source);

        let hints = inlay_hints(
            &state,
            uri,
            Range::new(Position::new(0, 0), Position::new(2, 0)),
        )
        .expect("inlay hints should be available");

        assert!(hints.is_empty());
    }

    #[test]
    fn inlay_hints_respect_requested_range() {
        let project = TestProject::new("inlay-range");
        let source = "let first = 1;\nlet second = true;\nfirst\n";
        let (state, uri) = project.open("main.hern", source);

        let hints = inlay_hints(
            &state,
            uri,
            Range::new(Position::new(1, 0), Position::new(1, 20)),
        )
        .expect("inlay hints should be available");

        assert_eq!(hints.len(), 1);
        assert_eq!(hints[0].position, Position::new(1, 10));
        assert!(matches!(&hints[0].label, InlayHintLabel::String(text) if text == ": bool"));
    }

    #[test]
    fn inlay_hints_show_unannotated_function_param_types() {
        let project = TestProject::new("inlay-fn-params");
        let source = "fn id(value) { let out: int = value; out }\nid(1)\n";
        let (state, uri) = project.open("main.hern", source);

        let hints = inlay_hints(
            &state,
            uri,
            Range::new(Position::new(0, 0), Position::new(2, 0)),
        )
        .expect("inlay hints should be available");

        assert!(hints.iter().any(|hint| {
            hint.position == Position::new(0, 11)
                && matches!(&hint.label, InlayHintLabel::String(text) if text == ": int")
        }));
    }

    #[test]
    fn inlay_hints_show_generic_function_param_types() {
        let project = TestProject::new("inlay-fn-params-generic");
        let source = "fn first(a, b) { a }\nfirst(1, true)\n";
        let (state, uri) = project.open("main.hern", source);

        let hints = inlay_hints(
            &state,
            uri,
            Range::new(Position::new(0, 0), Position::new(2, 0)),
        )
        .expect("inlay hints should be available");

        assert!(hints.iter().any(|hint| {
            hint.position == Position::new(0, 10)
                && matches!(&hint.label, InlayHintLabel::String(text) if text == ": 'a")
        }));
        assert!(hints.iter().any(|hint| {
            hint.position == Position::new(0, 13)
                && matches!(&hint.label, InlayHintLabel::String(text) if text == ": 'b")
        }));
    }

    #[test]
    fn inlay_hints_skip_annotated_function_params() {
        let project = TestProject::new("inlay-fn-param-explicit");
        let source = "fn id(value: int) { value }\nid(1)\n";
        let (state, uri) = project.open("main.hern", source);

        let hints = inlay_hints(
            &state,
            uri,
            Range::new(Position::new(0, 0), Position::new(2, 0)),
        )
        .expect("inlay hints should be available");

        assert!(
            hints
                .iter()
                .all(|hint| hint.position != Position::new(0, 11))
        );
    }

    #[test]
    fn inlay_hints_show_inferred_function_return_type() {
        let project = TestProject::new("inlay-fn-return");
        let source = "fn id(value: int) { value }\nid(1)\n";
        let (state, uri) = project.open("main.hern", source);

        let hints = inlay_hints(
            &state,
            uri,
            Range::new(Position::new(0, 0), Position::new(2, 0)),
        )
        .expect("inlay hints should be available");

        assert!(hints.iter().any(|hint| {
            hint.position == Position::new(0, 18)
                && matches!(&hint.label, InlayHintLabel::String(text) if text == " -> int")
        }));
    }

    #[test]
    fn inlay_hints_skip_explicit_function_return_type() {
        let project = TestProject::new("inlay-fn-return-explicit");
        let source = "fn id(value: int) -> int { value }\nid(1)\n";
        let (state, uri) = project.open("main.hern", source);

        let hints = inlay_hints(
            &state,
            uri,
            Range::new(Position::new(0, 0), Position::new(2, 0)),
        )
        .expect("inlay hints should be available");

        assert!(
            hints
                .iter()
                .all(|hint| hint.position != Position::new(0, 25))
        );
    }
}
