use super::state::{ServerState, cached_analysis};
use super::uri::{path_to_uri, source_span_to_range, uri_to_path};
use super::workspace::load_document_graph;
use hern_core::ast::SourcePosition;
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
    *fallback = Some(load_document_graph(state, uri).ok()?);
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
    let definition = index.definition_for_reference_at(SourcePosition {
        line: position.line,
        col: position.col,
    })?;
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
