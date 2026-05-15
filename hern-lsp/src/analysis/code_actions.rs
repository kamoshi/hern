use super::hover::{ast_type_to_string, ty_to_display_string};
use super::snapshot::{SnapshotMode, analysis_snapshot};
use super::state::ServerState;
use super::uri::source_span_to_range;
use hern_core::ast::{
    Expr, ExprKind, ImplDef, Pattern, SourceSpan, Stmt, TraitDef, TraitMethod, Type,
};
use hern_core::module::{GraphInference, ModuleGraph};
use hern_core::types::Ty;
use lsp_types::{
    CodeAction, CodeActionContext, CodeActionKind, CodeActionOrCommand, Position, Range, TextEdit,
    Uri, WorkspaceEdit,
};
use std::collections::{HashMap, HashSet};

pub(crate) fn code_actions(
    state: &ServerState,
    uri: Uri,
    range: Range,
    _context: CodeActionContext,
) -> Vec<CodeActionOrCommand> {
    let Some(snapshot) = analysis_snapshot(state, &uri, SnapshotMode::PreferTyped) else {
        return Vec::new();
    };
    let source = snapshot.source();
    let graph = snapshot.graph();
    let inference = snapshot.inference();
    let Some((module_name, program)) = snapshot.module() else {
        return Vec::new();
    };
    let binding_types =
        inference.and_then(|inference| inference.binding_types_for_module(module_name));

    let mut actions = Vec::new();
    let mut ctx = CodeActionCtx {
        uri: &uri,
        range,
        source,
        graph,
        inference,
        module_name,
        binding_types,
        actions: &mut actions,
    };
    for stmt in &program.stmts {
        collect_code_actions_for_stmt(stmt, &mut ctx);
    }
    actions
}

struct CodeActionCtx<'a> {
    uri: &'a Uri,
    range: Range,
    source: &'a str,
    graph: &'a ModuleGraph,
    inference: Option<&'a GraphInference>,
    module_name: &'a str,
    binding_types: Option<&'a HashMap<SourceSpan, Ty>>,
    actions: &'a mut Vec<CodeActionOrCommand>,
}

fn collect_code_actions_for_stmt(stmt: &Stmt, ctx: &mut CodeActionCtx<'_>) {
    match stmt {
        Stmt::Let {
            pat,
            ty: None,
            value,
            ..
        } => {
            if let Pattern::Variable(name, name_span) = pat
                && ranges_intersect(source_span_to_range(*name_span), ctx.range)
                && let Some(ty) = ctx
                    .binding_types
                    .and_then(|binding_types| binding_types.get(name_span))
                && let Some(type_text) = annotation_type_text(ty)
            {
                ctx.actions.push(add_type_annotation_action(
                    ctx.uri.clone(),
                    name,
                    *name_span,
                    type_text,
                ));
            }
            collect_code_actions_for_expr(value, ctx);
        }
        Stmt::Let { value, .. } => {
            collect_code_actions_for_expr(value, ctx);
        }
        Stmt::Fn { body, .. } | Stmt::Op { body, .. } => {
            collect_code_actions_for_expr(body, ctx);
        }
        Stmt::Impl(impl_def) => {
            collect_missing_trait_method_action(impl_def, ctx);
            for method in &impl_def.methods {
                collect_code_actions_for_expr(&method.body, ctx);
            }
        }
        Stmt::InherentImpl(impl_def) => {
            for method in &impl_def.methods {
                collect_code_actions_for_expr(&method.body, ctx);
            }
        }
        Stmt::TestBlock { stmts, .. } => {
            for stmt in stmts {
                collect_code_actions_for_stmt(stmt, ctx);
            }
        }
        Stmt::Expr(expr) => collect_code_actions_for_expr(expr, ctx),
        Stmt::Trait(_) | Stmt::Type(_) | Stmt::TypeAlias { .. } | Stmt::Extern { .. } => {}
    }
}

fn collect_code_actions_for_expr(expr: &Expr, ctx: &mut CodeActionCtx<'_>) {
    match &expr.kind {
        ExprKind::Block { stmts, final_expr } => {
            for stmt in stmts {
                collect_code_actions_for_stmt(stmt, ctx);
            }
            if let Some(expr) = final_expr {
                collect_code_actions_for_expr(expr, ctx);
            }
        }
        ExprKind::Grouped(inner)
        | ExprKind::Not(inner)
        | ExprKind::Loop(inner)
        | ExprKind::Break(Some(inner))
        | ExprKind::Return(Some(inner))
        | ExprKind::FieldAccess { expr: inner, .. }
        | ExprKind::Lambda { body: inner, .. } => {
            collect_code_actions_for_expr(inner, ctx);
        }
        ExprKind::Neg { operand, .. } => collect_code_actions_for_expr(operand, ctx),
        ExprKind::Assign { target, value } => {
            collect_code_actions_for_expr(target, ctx);
            collect_code_actions_for_expr(value, ctx);
        }
        ExprKind::Binary { lhs, rhs, .. } => {
            collect_code_actions_for_expr(lhs, ctx);
            collect_code_actions_for_expr(rhs, ctx);
        }
        ExprKind::Range { start, end, .. } => {
            if let Some(start) = start {
                collect_code_actions_for_expr(start, ctx);
            }
            if let Some(end) = end {
                collect_code_actions_for_expr(end, ctx);
            }
        }
        ExprKind::Call { callee, args, .. } => {
            collect_code_actions_for_expr(callee, ctx);
            for arg in args {
                collect_code_actions_for_expr(arg, ctx);
            }
        }
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
        } => {
            collect_code_actions_for_expr(cond, ctx);
            collect_code_actions_for_expr(then_branch, ctx);
            collect_code_actions_for_expr(else_branch, ctx);
        }
        ExprKind::Match { scrutinee, arms } => {
            collect_code_actions_for_expr(scrutinee, ctx);
            for (_, body) in arms {
                collect_code_actions_for_expr(body, ctx);
            }
        }
        ExprKind::Tuple(items) => {
            for item in items {
                collect_code_actions_for_expr(item, ctx);
            }
        }
        ExprKind::Array(entries) => {
            for entry in entries {
                collect_code_actions_for_expr(entry.expr(), ctx);
            }
        }
        ExprKind::Record(entries) => {
            for entry in entries {
                collect_code_actions_for_expr(entry.expr(), ctx);
            }
        }
        ExprKind::For { iterable, body, .. } => {
            collect_code_actions_for_expr(iterable, ctx);
            collect_code_actions_for_expr(body, ctx);
        }
        ExprKind::Index { receiver, key, .. } => {
            collect_code_actions_for_expr(receiver, ctx);
            collect_code_actions_for_expr(key, ctx);
        }
        ExprKind::AssociatedAccess { .. } => {}
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

fn collect_missing_trait_method_action(impl_def: &ImplDef, ctx: &mut CodeActionCtx<'_>) {
    if !ranges_intersect(source_span_to_range(impl_def.span), ctx.range) {
        return;
    }

    let Some(trait_def) = trait_def_for_impl(impl_def, ctx.graph, ctx.inference, ctx.module_name)
    else {
        return;
    };
    let implemented = impl_def
        .methods
        .iter()
        .map(|method| method.name.as_str())
        .collect::<HashSet<_>>();
    let missing = trait_def
        .methods
        .iter()
        .filter(|method| !implemented.contains(method.name.as_str()))
        .collect::<Vec<_>>();
    if missing.is_empty() {
        return;
    }

    let insert_position = impl_closing_brace_position(impl_def);
    let insert_text = missing_trait_method_insert_text(
        ctx.source,
        insert_position,
        impl_def,
        &trait_def,
        &missing,
    );
    let title = if missing.len() == 1 {
        format!(
            "Add missing `{}` method for `{}`",
            missing[0].name, trait_def.name
        )
    } else {
        format!(
            "Add {} missing methods for `{}`",
            missing.len(),
            trait_def.name
        )
    };

    ctx.actions
        .push(CodeActionOrCommand::CodeAction(CodeAction {
            title,
            kind: Some(CodeActionKind::QUICKFIX),
            diagnostics: None,
            edit: Some(WorkspaceEdit {
                changes: Some(HashMap::from([(
                    ctx.uri.clone(),
                    vec![TextEdit {
                        range: Range::new(insert_position, insert_position),
                        new_text: insert_text,
                    }],
                )])),
                document_changes: None,
                change_annotations: None,
            }),
            command: None,
            is_preferred: Some(true),
            disabled: None,
            data: None,
        }));
}

fn trait_def_for_impl(
    impl_def: &ImplDef,
    graph: &ModuleGraph,
    inference: Option<&GraphInference>,
    module_name: &str,
) -> Option<TraitDef> {
    if let Some(trait_def) = inference
        .and_then(|inference| inference.module_env_for_module(module_name))
        .and_then(|module_env| module_env.trait_def(&impl_def.trait_name))
    {
        return Some(trait_def.clone());
    }

    graph
        .modules
        .get(module_name)
        .and_then(|program| trait_def_in_program(program, &impl_def.trait_name))
        .or_else(|| trait_def_in_program(&graph.prelude, &impl_def.trait_name))
        .or_else(|| {
            graph
                .modules
                .values()
                .find_map(|program| trait_def_in_program(program, &impl_def.trait_name))
        })
        .cloned()
}

fn trait_def_in_program<'a>(
    program: &'a hern_core::ast::Program,
    trait_name: &str,
) -> Option<&'a TraitDef> {
    program.stmts.iter().find_map(|stmt| match stmt {
        Stmt::Trait(trait_def) if trait_def.name == trait_name => Some(trait_def),
        _ => None,
    })
}

fn impl_closing_brace_position(impl_def: &ImplDef) -> Position {
    let mut position = source_span_to_range(impl_def.span).end;
    position.character = position.character.saturating_sub(1);
    position
}

fn missing_trait_method_insert_text(
    source: &str,
    insert_position: Position,
    impl_def: &ImplDef,
    trait_def: &TraitDef,
    missing: &[&TraitMethod],
) -> String {
    let close_indent = line_indent(source, insert_position.line);
    let method_indent = format!("{close_indent}  ");
    let body_indent = format!("{close_indent}    ");
    let stubs = missing
        .iter()
        .map(|method| trait_method_stub(method, impl_def, trait_def, &method_indent, &body_indent))
        .collect::<Vec<_>>()
        .join("\n\n");
    format!("\n{stubs}\n{close_indent}")
}

fn trait_method_stub(
    method: &TraitMethod,
    impl_def: &ImplDef,
    trait_def: &TraitDef,
    method_indent: &str,
    body_indent: &str,
) -> String {
    let params = method
        .params
        .iter()
        .map(|(name, ty)| {
            let ty = substitute_impl_trait_args(ty, impl_def, trait_def);
            format!("{name}: {}", ast_type_to_string(&ty))
        })
        .collect::<Vec<_>>()
        .join(", ");
    let ret_type = ast_type_to_string(&substitute_impl_trait_args(
        &method.ret_type,
        impl_def,
        trait_def,
    ));
    format!(
        "{method_indent}fn {}({params}) -> {ret_type} {{\n{body_indent}todo(\"implement {}\")\n{method_indent}}}",
        method.name, method.name
    )
}

fn substitute_impl_trait_args(ty: &Type, impl_def: &ImplDef, trait_def: &TraitDef) -> Type {
    trait_def
        .params
        .iter()
        .zip(impl_def.trait_args.iter())
        .fold(ty.clone(), |ty, (param, arg)| {
            substitute_trait_param(&ty, param, arg)
        })
}

fn substitute_trait_param(ty: &Type, param: &str, target: &Type) -> Type {
    match ty {
        Type::Var(name) if name == param => target.clone(),
        Type::App(con, args) if matches!(con.as_ref(), Type::Var(name) if name == param) => {
            let args = args
                .iter()
                .map(|arg| substitute_trait_param(arg, param, target))
                .collect::<Vec<_>>();
            if args.len() == 1 {
                apply_type_hole(target, &args[0])
            } else {
                Type::App(Box::new(target.clone()), args)
            }
        }
        Type::App(con, args) => Type::App(
            Box::new(substitute_trait_param(con, param, target)),
            args.iter()
                .map(|arg| substitute_trait_param(arg, param, target))
                .collect(),
        ),
        Type::Func(params, ret) => Type::Func(
            params
                .iter()
                .map(|param_ty| hern_core::ast::TypeParam {
                    ty: substitute_trait_param(&param_ty.ty, param, target),
                    mut_place: param_ty.mut_place,
                })
                .collect(),
            hern_core::ast::TypeReturn {
                ty: Box::new(substitute_trait_param(&ret.ty, param, target)),
                mut_place: ret.mut_place,
            },
        ),
        Type::Tuple(items) => Type::Tuple(
            items
                .iter()
                .map(|item| substitute_trait_param(item, param, target))
                .collect(),
        ),
        Type::Record(fields, open) => Type::Record(
            fields
                .iter()
                .map(|(name, field_ty)| {
                    (
                        name.clone(),
                        substitute_trait_param(field_ty, param, target),
                    )
                })
                .collect(),
            *open,
        ),
        _ => ty.clone(),
    }
}

fn apply_type_hole(target: &Type, arg: &Type) -> Type {
    if type_has_hole(target) {
        // A `*` in an impl target is a placeholder for the implemented type
        // parameter. If several holes appear, they intentionally receive the
        // same argument; use explicit trait parameters for independent holes.
        substitute_type_hole(target, arg)
    } else {
        Type::App(Box::new(target.clone()), vec![arg.clone()])
    }
}

fn type_has_hole(ty: &Type) -> bool {
    match ty {
        Type::Hole => true,
        Type::App(con, args) => type_has_hole(con) || args.iter().any(type_has_hole),
        Type::Func(params, ret) => {
            params.iter().any(|param| type_has_hole(&param.ty)) || type_has_hole(&ret.ty)
        }
        Type::Tuple(items) => items.iter().any(type_has_hole),
        Type::Record(fields, _) => fields.iter().any(|(_, ty)| type_has_hole(ty)),
        _ => false,
    }
}

fn substitute_type_hole(ty: &Type, arg: &Type) -> Type {
    match ty {
        Type::Hole => arg.clone(),
        Type::App(con, args) => Type::App(
            Box::new(substitute_type_hole(con, arg)),
            args.iter()
                .map(|item| substitute_type_hole(item, arg))
                .collect(),
        ),
        Type::Func(params, ret) => Type::Func(
            params
                .iter()
                .map(|param| hern_core::ast::TypeParam {
                    ty: substitute_type_hole(&param.ty, arg),
                    mut_place: param.mut_place,
                })
                .collect(),
            hern_core::ast::TypeReturn {
                ty: Box::new(substitute_type_hole(&ret.ty, arg)),
                mut_place: ret.mut_place,
            },
        ),
        Type::Tuple(items) => Type::Tuple(
            items
                .iter()
                .map(|item| substitute_type_hole(item, arg))
                .collect(),
        ),
        Type::Record(fields, open) => Type::Record(
            fields
                .iter()
                .map(|(name, ty)| (name.clone(), substitute_type_hole(ty, arg)))
                .collect(),
            *open,
        ),
        _ => ty.clone(),
    }
}

fn line_indent(source: &str, line: u32) -> String {
    source
        .lines()
        .nth(line as usize)
        .unwrap_or_default()
        .chars()
        .take_while(|ch| ch.is_whitespace())
        .collect()
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
        assert_eq!(edits[0].new_text, ": int");
    }

    #[test]
    fn code_action_absent_when_binding_already_has_annotation() {
        let project = TestProject::new("code-action-existing-type");
        let source = "let value: int = 1;\nvalue\n";
        let (state, uri) = project.open("main.hern", source);

        let actions = code_actions(
            &state,
            uri,
            Range::new(Position::new(0, 4), Position::new(0, 9)),
            CodeActionContext::default(),
        );

        assert!(actions.is_empty());
    }

    #[test]
    fn code_action_adds_missing_local_trait_methods() {
        let project = TestProject::new("code-action-missing-trait-methods");
        let source = "\
trait Label 'a {
  fn label(value: 'a) -> string
  fn score(value: 'a) -> int
}

type Boxed = Boxed(int)

impl Label for Boxed {
}
";
        let (state, uri) = project.open("main.hern", source);

        let action = code_actions(
            &state,
            uri.clone(),
            Range::new(Position::new(7, 0), Position::new(8, 1)),
            CodeActionContext::default(),
        )
        .into_iter()
        .find_map(|action| match action {
            CodeActionOrCommand::CodeAction(action)
                if action.title == "Add 2 missing methods for `Label`" =>
            {
                Some(action)
            }
            _ => None,
        })
        .expect("missing method action should be available");

        let edit = action.edit.expect("action should include edit");
        let changes = edit.changes.expect("edit should use simple changes");
        let edits = changes.get(&uri).expect("edit should target document");
        assert_eq!(edits[0].range.start, Position::new(8, 0));
        assert_eq!(
            edits[0].new_text,
            "\n  fn label(value: Boxed) -> string {\n    todo(\"implement label\")\n  }\n\n  fn score(value: Boxed) -> int {\n    todo(\"implement score\")\n  }\n"
        );
    }

    #[test]
    fn code_action_adds_missing_prelude_trait_method() {
        let project = TestProject::new("code-action-missing-prelude-trait-method");
        let source = "\
type Boxed = Boxed(int)

impl ToString for Boxed {
}
";
        let (state, uri) = project.open("main.hern", source);

        let action = code_actions(
            &state,
            uri.clone(),
            Range::new(Position::new(2, 0), Position::new(3, 1)),
            CodeActionContext::default(),
        )
        .into_iter()
        .find_map(|action| match action {
            CodeActionOrCommand::CodeAction(action)
                if action.title == "Add missing `to_string` method for `ToString`" =>
            {
                Some(action)
            }
            _ => None,
        })
        .expect("missing prelude trait method action should be available");

        let edit = action.edit.expect("action should include edit");
        let changes = edit.changes.expect("edit should use simple changes");
        let edits = changes.get(&uri).expect("edit should target document");
        assert_eq!(
            edits[0].new_text,
            "\n  fn to_string(self: Boxed) -> string {\n    todo(\"implement to_string\")\n  }\n"
        );
    }

    #[test]
    fn code_action_substitutes_higher_kinded_trait_targets() {
        let project = TestProject::new("code-action-missing-hkt-trait-method");
        let source = "\
trait Mapper 'f {
  fn map(value: 'f('a), f: fn('a) -> 'b) -> 'f('b)
}

impl Mapper for Result(*, string) {
}
";
        let (state, uri) = project.open("main.hern", source);

        let action = code_actions(
            &state,
            uri.clone(),
            Range::new(Position::new(4, 0), Position::new(5, 1)),
            CodeActionContext::default(),
        )
        .into_iter()
        .find_map(|action| match action {
            CodeActionOrCommand::CodeAction(action)
                if action.title == "Add missing `map` method for `Mapper`" =>
            {
                Some(action)
            }
            _ => None,
        })
        .expect("missing HKT trait method action should be available");

        let edit = action.edit.expect("action should include edit");
        let changes = edit.changes.expect("edit should use simple changes");
        let edits = changes.get(&uri).expect("edit should target document");
        assert_eq!(
            edits[0].new_text,
            "\n  fn map(value: Result('a, string), f: fn('a) -> 'b) -> Result('b, string) {\n    todo(\"implement map\")\n  }\n"
        );
    }

    #[test]
    fn code_action_does_not_use_trait_from_unimported_module() {
        let project = TestProject::new("code-action-unimported-trait");
        project.write(
            "dep.hern",
            "\
trait Ghost 'a {
  fn haunt(value: 'a) -> string
}
",
        );
        let source = "\
type Boxed = Boxed(int)

impl Ghost for Boxed {
}
";
        let (state, uri) = project.open("main.hern", source);

        let actions = code_actions(
            &state,
            uri,
            Range::new(Position::new(2, 0), Position::new(3, 1)),
            CodeActionContext::default(),
        );

        assert!(
            actions.into_iter().all(|action| match action {
                CodeActionOrCommand::CodeAction(action) =>
                    action.title != "Add missing `haunt` method for `Ghost`",
                CodeActionOrCommand::Command(_) => true,
            }),
            "unimported traits should not produce missing-method stubs"
        );
    }
}
