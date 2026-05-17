use super::state::{ServerState, cached_analysis};
use super::uri::{path_to_uri, source_span_to_range, uri_to_path};
use super::workspace::load_document_graph_recovering;
use hern_core::ast::{Expr, ExprKind, Program, SourcePosition, SourceSpan, Stmt, Type};
use hern_core::module::ModuleGraph;
use hern_core::source_index::index_program;
use lsp_types::{DocumentHighlight, DocumentHighlightKind, Location, Position, Uri};

/// Returns a reference to the module graph for `uri`, using the cache when valid
/// and falling back to a fresh load. The returned reference borrows either `state`
/// (cached path) or `fallback` (fresh path); callers must declare both slots.
fn resolve_graph<'a>(
    state: &'a ServerState,
    uri: &Uri,
    fallback: &'a mut Option<ModuleGraph>,
) -> Option<&'a ModuleGraph> {
    if let Some(analysis) = cached_analysis(state, uri) {
        return Some(&analysis.graph);
    }
    *fallback = Some(load_document_graph_recovering(state, uri)?);
    fallback.as_ref()
}

pub(crate) fn definition(state: &ServerState, uri: Uri, position: Position) -> Option<Location> {
    let path = uri_to_path(&uri)?;
    let mut fallback = None;
    let graph = resolve_graph(state, &uri, &mut fallback)?;
    let (_, program) = graph.module_for_path(&path)?;
    let index = index_program(program);
    let position = SourcePosition {
        line: position.line as usize + 1,
        col: position.character as usize + 1,
    };
    if let Some(reference) = index.import_member_reference_at(position) {
        let target_program = graph.module(&reference.module_name)?;
        let target_path = graph.module_path(&reference.module_name)?;
        let target_index = index_program(target_program);
        let target_definition = target_index.definition_named(&reference.member_name)?;
        return Some(Location::new(
            path_to_uri(target_path)?,
            source_span_to_range(target_definition.location.span),
        ));
    }
    if let Some(span) = associated_definition_span_at(program, position) {
        return Some(Location::new(uri, source_span_to_range(span)));
    }
    let definition = index
        .definition_for_reference_at(SourcePosition {
            line: position.line,
            col: position.col,
        })
        .or_else(|| index.definition_at(position))?;
    Some(Location::new(
        uri,
        source_span_to_range(definition.location.span),
    ))
}

pub(crate) fn references(
    state: &ServerState,
    uri: Uri,
    position: Position,
    include_declaration: bool,
) -> Vec<Location> {
    let Some(path) = uri_to_path(&uri) else {
        return Vec::new();
    };
    let mut fallback = None;
    let Some(graph) = resolve_graph(state, &uri, &mut fallback) else {
        return Vec::new();
    };
    let Some((_, program)) = graph.module_for_path(&path) else {
        return Vec::new();
    };
    let index = index_program(program);
    let position = SourcePosition {
        line: position.line as usize + 1,
        col: position.character as usize + 1,
    };

    if let Some(import_ref) = index.import_member_reference_at(position) {
        let module_name = import_ref.module_name.clone();
        let member_name = import_ref.member_name.clone();
        references_for_import_member(graph, &module_name, &member_name, include_declaration)
    } else {
        let spans = index.references_for_symbol_at(position, include_declaration);
        spans
            .into_iter()
            .map(|span| Location::new(uri.clone(), source_span_to_range(span)))
            .collect()
    }
}

fn associated_definition_span_at(
    program: &Program,
    position: SourcePosition,
) -> Option<SourceSpan> {
    program
        .stmts
        .iter()
        .find_map(|stmt| associated_definition_span_in_stmt(program, stmt, position))
}

fn associated_definition_span_in_stmt(
    program: &Program,
    stmt: &Stmt,
    position: SourcePosition,
) -> Option<SourceSpan> {
    match stmt {
        Stmt::Let { value, .. } | Stmt::Expr(value) => {
            associated_definition_span_in_expr(program, value, position)
        }
        Stmt::Fn { body, .. } | Stmt::Op { body, .. } => {
            associated_definition_span_in_expr(program, body, position)
        }
        Stmt::Impl(impl_def) => impl_def
            .methods
            .iter()
            .find_map(|method| associated_definition_span_in_expr(program, &method.body, position)),
        Stmt::InherentImpl(impl_def) => impl_def
            .methods
            .iter()
            .find_map(|method| associated_definition_span_in_expr(program, &method.body, position)),
        Stmt::TestBlock { stmts, .. } => stmts
            .iter()
            .find_map(|stmt| associated_definition_span_in_stmt(program, stmt, position)),
        Stmt::RecBlock { stmts, .. } => stmts
            .iter()
            .find_map(|stmt| associated_definition_span_in_stmt(program, stmt, position)),
        Stmt::Trait(_) | Stmt::Type(_) | Stmt::TypeAlias { .. } | Stmt::Extern { .. } => None,
    }
}

fn associated_definition_span_in_expr(
    program: &Program,
    expr: &Expr,
    position: SourcePosition,
) -> Option<SourceSpan> {
    if !contains(expr.span, position) {
        return None;
    }
    if let ExprKind::AssociatedAccess {
        target: Type::Ident(target_name),
        target_span,
        member,
        member_span,
        ..
    } = &expr.kind
    {
        if contains(*target_span, position) {
            return top_level_definition_span(program, target_name);
        }
        if contains(*member_span, position) {
            return associated_member_definition_span(program, target_name, member);
        }
    }

    match &expr.kind {
        ExprKind::Grouped(inner)
        | ExprKind::Not(inner)
        | ExprKind::Loop(inner)
        | ExprKind::Break(Some(inner))
        | ExprKind::Return(Some(inner))
        | ExprKind::FieldAccess { expr: inner, .. }
        | ExprKind::Lambda { body: inner, .. } => {
            associated_definition_span_in_expr(program, inner, position)
        }
        ExprKind::Neg { operand, .. } => {
            associated_definition_span_in_expr(program, operand, position)
        }
        ExprKind::Assign { target, value } => {
            associated_definition_span_in_expr(program, target, position)
                .or_else(|| associated_definition_span_in_expr(program, value, position))
        }
        ExprKind::Binary { lhs, rhs, .. } => {
            associated_definition_span_in_expr(program, lhs, position)
                .or_else(|| associated_definition_span_in_expr(program, rhs, position))
        }
        ExprKind::Range { start, end, .. } => start
            .as_deref()
            .and_then(|expr| associated_definition_span_in_expr(program, expr, position))
            .or_else(|| {
                end.as_deref()
                    .and_then(|expr| associated_definition_span_in_expr(program, expr, position))
            }),
        ExprKind::Call { callee, args, .. } => {
            associated_definition_span_in_expr(program, callee, position).or_else(|| {
                args.iter()
                    .find_map(|arg| associated_definition_span_in_expr(program, arg, position))
            })
        }
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
        } => associated_definition_span_in_expr(program, cond, position)
            .or_else(|| associated_definition_span_in_expr(program, then_branch, position))
            .or_else(|| associated_definition_span_in_expr(program, else_branch, position)),
        ExprKind::Match { scrutinee, arms } => {
            associated_definition_span_in_expr(program, scrutinee, position).or_else(|| {
                arms.iter().find_map(|(_, body)| {
                    associated_definition_span_in_expr(program, body, position)
                })
            })
        }
        ExprKind::Block { stmts, final_expr } => stmts
            .iter()
            .find_map(|stmt| associated_definition_span_in_stmt(program, stmt, position))
            .or_else(|| {
                final_expr
                    .as_deref()
                    .and_then(|expr| associated_definition_span_in_expr(program, expr, position))
            }),
        ExprKind::Tuple(items) => items
            .iter()
            .find_map(|item| associated_definition_span_in_expr(program, item, position)),
        ExprKind::Array(entries) => entries
            .iter()
            .find_map(|entry| associated_definition_span_in_expr(program, entry.expr(), position)),
        ExprKind::Record(entries) => entries
            .iter()
            .find_map(|entry| associated_definition_span_in_expr(program, entry.expr(), position)),
        ExprKind::For { iterable, body, .. } => {
            associated_definition_span_in_expr(program, iterable, position)
                .or_else(|| associated_definition_span_in_expr(program, body, position))
        }
        ExprKind::Index { receiver, key, .. } => {
            associated_definition_span_in_expr(program, receiver, position)
                .or_else(|| associated_definition_span_in_expr(program, key, position))
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
        | ExprKind::Unit => None,
    }
}

fn top_level_definition_span(program: &Program, name: &str) -> Option<SourceSpan> {
    program.stmts.iter().find_map(|stmt| match stmt {
        Stmt::Trait(trait_def) if trait_def.name == name => Some(trait_def.name_span),
        Stmt::Type(type_def) if type_def.name == name => Some(type_def.name_span),
        Stmt::TypeAlias {
            name: alias,
            name_span,
            ..
        } if alias == name => Some(*name_span),
        _ => None,
    })
}

fn associated_member_definition_span(
    program: &Program,
    target_name: &str,
    member: &str,
) -> Option<SourceSpan> {
    program.stmts.iter().find_map(|stmt| match stmt {
        Stmt::Trait(trait_def) if trait_def.name == target_name => trait_def
            .methods
            .iter()
            .find(|method| method.name == member)
            .map(|method| method.name_span),
        Stmt::InherentImpl(impl_def) if type_ident_name(&impl_def.target) == Some(target_name) => {
            impl_def
                .methods
                .iter()
                .find(|method| method.name == member)
                .map(|method| method.name_span)
        }
        _ => None,
    })
}

fn type_ident_name(ty: &Type) -> Option<&str> {
    match ty {
        Type::Ident(name) => Some(name),
        _ => None,
    }
}

fn contains(span: SourceSpan, pos: SourcePosition) -> bool {
    let start = (span.start_line, span.start_col);
    let end = (span.end_line, span.end_col);
    let cursor = (pos.line, pos.col);
    cursor >= start && cursor < end
}

pub(crate) fn document_highlights(
    state: &ServerState,
    uri: Uri,
    position: Position,
) -> Vec<DocumentHighlight> {
    let Some(path) = uri_to_path(&uri) else {
        return Vec::new();
    };
    let mut fallback = None;
    let Some(graph) = resolve_graph(state, &uri, &mut fallback) else {
        return Vec::new();
    };
    let Some((_, program)) = graph.module_for_path(&path) else {
        return Vec::new();
    };
    let index = index_program(program);
    let position = SourcePosition {
        line: position.line as usize + 1,
        col: position.character as usize + 1,
    };

    if let Some(import_ref) = index.import_member_reference_at(position) {
        let mut spans =
            index.import_member_references_for(&import_ref.module_name, &import_ref.member_name);
        spans.sort_by_key(|span| (span.start_line, span.start_col));
        return spans
            .into_iter()
            .map(|span| DocumentHighlight {
                range: source_span_to_range(span),
                kind: Some(DocumentHighlightKind::READ),
            })
            .collect();
    }

    let Some(definition) = index
        .definition_at(position)
        .or_else(|| index.definition_for_reference_at(position))
    else {
        return Vec::new();
    };
    index
        .references_for_symbol_at(position, true)
        .into_iter()
        .map(|span| DocumentHighlight {
            range: source_span_to_range(span),
            kind: Some(if span == definition.location.span {
                DocumentHighlightKind::WRITE
            } else {
                DocumentHighlightKind::READ
            }),
        })
        .collect()
}

/// Collects all `Location`s for references to `member_name` exported from `module_name`,
/// scanning every module in the graph in graph order. Optionally includes the definition site
/// in the target module when `include_declaration` is true.
fn references_for_import_member(
    graph: &hern_core::module::ModuleGraph,
    module_name: &str,
    member_name: &str,
    include_declaration: bool,
) -> Vec<Location> {
    let mut locations = Vec::new();

    if include_declaration && let Some(target_program) = graph.module(module_name) {
        let target_index = index_program(target_program);
        if let Some(def) = target_index.definition_named(member_name)
            && let Some(target_path) = graph.module_path(module_name)
            && let Some(target_uri) = path_to_uri(target_path)
        {
            locations.push(Location::new(
                target_uri,
                source_span_to_range(def.location.span),
            ));
        }
    }

    for name in &graph.order {
        let Some(prog) = graph.module(name) else {
            continue;
        };
        let prog_index = index_program(prog);
        let mut spans = prog_index.import_member_references_for(module_name, member_name);
        if spans.is_empty() {
            continue;
        }
        let Some(module_path) = graph.module_path(name) else {
            continue;
        };
        let Some(module_uri) = path_to_uri(module_path) else {
            continue;
        };
        spans.sort_by_key(|s| (s.start_line, s.start_col));
        for span in spans {
            locations.push(Location::new(
                module_uri.clone(),
                source_span_to_range(span),
            ));
        }
    }

    locations
}
