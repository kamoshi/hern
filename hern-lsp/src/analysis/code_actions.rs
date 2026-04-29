use super::hover::ty_to_display_string;
use super::state::{ServerState, cached_analysis};
use super::uri::{source_span_to_range, uri_to_path};
use super::workspace::load_workspace_graphs;
use hern_core::ast::{Expr, ExprKind, Pattern, SourceSpan, Stmt};
use hern_core::types::Ty;
use lsp_types::{
    CodeAction, CodeActionContext, CodeActionKind, CodeActionOrCommand, Position, Range, TextEdit,
    Uri, WorkspaceEdit,
};
use std::collections::HashMap;

pub(crate) fn code_actions(
    state: &ServerState,
    uri: Uri,
    range: Range,
    _context: CodeActionContext,
) -> Vec<CodeActionOrCommand> {
    let Some(path) = uri_to_path(&uri) else {
        return Vec::new();
    };
    let fallback;
    let (graph, inference) = if let Some(analysis) = cached_analysis(state, &uri) {
        (&analysis.graph, &analysis.inference)
    } else {
        let Some(analysis) = load_workspace_graphs(state, &uri) else {
            return Vec::new();
        };
        fallback = analysis;
        (&fallback.graph, &fallback.inference)
    };
    let Some((module_name, program)) = graph.module_for_path(&path) else {
        return Vec::new();
    };
    let Some(binding_types) = inference.binding_types_for_module(module_name) else {
        return Vec::new();
    };

    let mut actions = Vec::new();
    for stmt in &program.stmts {
        collect_code_actions_for_stmt(stmt, &uri, range, binding_types, &mut actions);
    }
    actions
}

fn collect_code_actions_for_stmt(
    stmt: &Stmt,
    uri: &Uri,
    range: Range,
    binding_types: &HashMap<SourceSpan, Ty>,
    actions: &mut Vec<CodeActionOrCommand>,
) {
    match stmt {
        Stmt::Let {
            pat,
            ty: None,
            value,
            ..
        } => {
            if let Pattern::Variable(name, name_span) = pat {
                if ranges_intersect(source_span_to_range(*name_span), range)
                    && let Some(ty) = binding_types.get(name_span)
                    && let Some(type_text) = annotation_type_text(ty)
                {
                    actions.push(add_type_annotation_action(
                        uri.clone(),
                        name,
                        *name_span,
                        type_text,
                    ));
                }
            }
            collect_code_actions_for_expr(value, uri, range, binding_types, actions);
        }
        Stmt::Let { value, .. } => {
            collect_code_actions_for_expr(value, uri, range, binding_types, actions);
        }
        Stmt::Fn { body, .. } | Stmt::Op { body, .. } => {
            collect_code_actions_for_expr(body, uri, range, binding_types, actions);
        }
        Stmt::Impl(impl_def) => {
            for method in &impl_def.methods {
                collect_code_actions_for_expr(&method.body, uri, range, binding_types, actions);
            }
        }
        Stmt::Expr(expr) => collect_code_actions_for_expr(expr, uri, range, binding_types, actions),
        Stmt::Trait(_) | Stmt::Type(_) | Stmt::TypeAlias { .. } | Stmt::Extern { .. } => {}
    }
}

fn collect_code_actions_for_expr(
    expr: &Expr,
    uri: &Uri,
    range: Range,
    binding_types: &HashMap<SourceSpan, Ty>,
    actions: &mut Vec<CodeActionOrCommand>,
) {
    match &expr.kind {
        ExprKind::Block { stmts, final_expr } => {
            for stmt in stmts {
                collect_code_actions_for_stmt(stmt, uri, range, binding_types, actions);
            }
            if let Some(expr) = final_expr {
                collect_code_actions_for_expr(expr, uri, range, binding_types, actions);
            }
        }
        ExprKind::Not(inner)
        | ExprKind::Loop(inner)
        | ExprKind::Break(Some(inner))
        | ExprKind::Return(Some(inner))
        | ExprKind::FieldAccess { expr: inner, .. }
        | ExprKind::Lambda { body: inner, .. } => {
            collect_code_actions_for_expr(inner, uri, range, binding_types, actions);
        }
        ExprKind::Assign { target, value } => {
            collect_code_actions_for_expr(target, uri, range, binding_types, actions);
            collect_code_actions_for_expr(value, uri, range, binding_types, actions);
        }
        ExprKind::Binary { lhs, rhs, .. } => {
            collect_code_actions_for_expr(lhs, uri, range, binding_types, actions);
            collect_code_actions_for_expr(rhs, uri, range, binding_types, actions);
        }
        ExprKind::Call { callee, args, .. } => {
            collect_code_actions_for_expr(callee, uri, range, binding_types, actions);
            for arg in args {
                collect_code_actions_for_expr(arg, uri, range, binding_types, actions);
            }
        }
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
        } => {
            collect_code_actions_for_expr(cond, uri, range, binding_types, actions);
            collect_code_actions_for_expr(then_branch, uri, range, binding_types, actions);
            collect_code_actions_for_expr(else_branch, uri, range, binding_types, actions);
        }
        ExprKind::Match { scrutinee, arms } => {
            collect_code_actions_for_expr(scrutinee, uri, range, binding_types, actions);
            for (_, body) in arms {
                collect_code_actions_for_expr(body, uri, range, binding_types, actions);
            }
        }
        ExprKind::Tuple(items) | ExprKind::Array(items) => {
            for item in items {
                collect_code_actions_for_expr(item, uri, range, binding_types, actions);
            }
        }
        ExprKind::Record(fields) => {
            for (_, value) in fields {
                collect_code_actions_for_expr(value, uri, range, binding_types, actions);
            }
        }
        ExprKind::For { iterable, body, .. } => {
            collect_code_actions_for_expr(iterable, uri, range, binding_types, actions);
            collect_code_actions_for_expr(body, uri, range, binding_types, actions);
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

fn add_type_annotation_action(
    uri: Uri,
    name: &str,
    name_span: SourceSpan,
    type_text: String,
) -> CodeActionOrCommand {
    let insert_position = source_span_to_range(name_span).end;
    CodeActionOrCommand::CodeAction(CodeAction {
        title: format!("Add type annotation to `{name}`"),
        kind: Some(CodeActionKind::REFACTOR),
        diagnostics: None,
        edit: Some(WorkspaceEdit {
            changes: Some(HashMap::from([(
                uri,
                vec![TextEdit {
                    range: Range::new(insert_position, insert_position),
                    new_text: format!(": {type_text}"),
                }],
            )])),
            document_changes: None,
            change_annotations: None,
        }),
        command: None,
        is_preferred: Some(false),
        disabled: None,
        data: None,
    })
}

fn annotation_type_text(ty: &Ty) -> Option<String> {
    let text = ty_to_display_string(ty);
    (!text.contains('\n')).then_some(text)
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
    fn code_action_adds_inferred_type_annotation_to_simple_let() {
        let project = TestProject::new("code-action-type-annotation");
        let source = "let value = 1;\nvalue\n";
        let (state, uri) = project.open("main.hern", source);

        let actions = code_actions(
            &state,
            uri.clone(),
            Range::new(Position::new(0, 4), Position::new(0, 9)),
            CodeActionContext::default(),
        );

        let CodeActionOrCommand::CodeAction(action) = actions
            .into_iter()
            .next()
            .expect("annotation action should be available")
        else {
            panic!("expected code action");
        };
        assert_eq!(action.title, "Add type annotation to `value`");
        let edit = action.edit.expect("action should include edit");
        let changes = edit.changes.expect("edit should use simple changes");
        let edits = changes.get(&uri).expect("edit should target document");
        assert_eq!(edits[0].range.start, Position::new(0, 9));
        assert_eq!(edits[0].new_text, ": f64");
    }

    #[test]
    fn code_action_absent_when_binding_already_has_annotation() {
        let project = TestProject::new("code-action-existing-type");
        let source = "let value: f64 = 1;\nvalue\n";
        let (state, uri) = project.open("main.hern", source);

        let actions = code_actions(
            &state,
            uri,
            Range::new(Position::new(0, 4), Position::new(0, 9)),
            CodeActionContext::default(),
        );

        assert!(actions.is_empty());
    }
}
