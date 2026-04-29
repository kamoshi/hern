use super::state::{ServerState, cached_analysis};
use super::uri::{source_span_to_range, uri_to_path};
use super::workspace::load_document_graph;
use hern_core::ast::{SourcePosition, SourceSpan};
use hern_core::lex::{Lexer, Token};
use hern_core::module::ModuleGraph;
use hern_core::source_index::{DefinitionKind, SourceIndex, index_program};
use lsp_types::{Position, PrepareRenameResponse, TextEdit, Uri, WorkspaceEdit};
use std::collections::HashMap;

/// Returns `true` if `name` is a well-formed Hern identifier that is not a reserved keyword.
///
/// Uses the lexer to tokenize the candidate, so keyword detection stays in sync with
/// the lexer without requiring a manually-maintained duplicate list.
fn is_valid_identifier(name: &str) -> bool {
    let Ok(tokens) = Lexer::new(name).tokenize() else {
        return false;
    };
    // tokenize() always appends an Eof sentinel; expect exactly [Ident, Eof].
    matches!(
        tokens.as_slice(),
        [ident, eof]
        if matches!(ident.token, Token::Ident(_)) && matches!(eof.token, Token::Eof)
    )
}

fn renameable_definition_kind(kind: DefinitionKind) -> bool {
    matches!(kind, DefinitionKind::Function | DefinitionKind::Let)
}

struct RenameTarget {
    current_span: SourceSpan,
    /// All reference spans for the symbol, including the declaration.
    spans: Vec<SourceSpan>,
}

fn rename_target_at(
    index: &SourceIndex,
    position: SourcePosition,
) -> Result<Option<RenameTarget>, String> {
    // Reject rename when the cursor is on a *member access* of an imported module (e.g. `dep.value`),
    // because the definition lives in another file and cross-file rename is out of scope for now.
    // Renaming the import binding itself (e.g. `dep` in `let dep = import "dep"`) is allowed: it
    // is just a local let binding resolved by references_for_symbol_at like any other local.
    if index.import_member_reference_at(position).is_some() {
        return Err("rename of imported members is not supported".to_string());
    }

    let Some(definition) = index
        .definition_at(position)
        .or_else(|| index.definition_for_reference_at(position))
    else {
        return Ok(None);
    };
    if !renameable_definition_kind(definition.kind) {
        return Err(format!(
            "rename is not supported for {:?} symbols",
            definition.kind
        ));
    }

    let spans = index.references_for_symbol_at(position, true);
    let current_span = spans
        .iter()
        .copied()
        .find(|span| source_span_contains_position(*span, position))
        .unwrap_or(definition.location.span);

    Ok(Some(RenameTarget {
        current_span,
        spans,
    }))
}

fn source_span_contains_position(span: SourceSpan, position: SourcePosition) -> bool {
    let start = (span.start_line, span.start_col);
    let end = (span.end_line, span.end_col);
    let position = (position.line, position.col);
    position >= start && position < end
}

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

pub(crate) fn prepare_rename(
    state: &ServerState,
    uri: Uri,
    position: Position,
) -> Result<Option<PrepareRenameResponse>, String> {
    let Some(path) = uri_to_path(&uri) else {
        return Ok(None);
    };
    let mut fallback = None;
    let Some(graph) = resolve_graph(state, &uri, &mut fallback) else {
        return Ok(None);
    };
    let Some((_, program)) = graph.module_for_path(&path) else {
        return Ok(None);
    };
    let index = index_program(program);
    let position = SourcePosition {
        line: position.line as usize + 1,
        col: position.character as usize + 1,
    };
    let Some(target) = rename_target_at(&index, position)? else {
        return Ok(None);
    };
    Ok(Some(PrepareRenameResponse::Range(source_span_to_range(
        target.current_span,
    ))))
}

/// Renames the symbol at `position` in `uri` to `new_name`.
///
/// Returns `Ok(Some(edit))` on success, `Ok(None)` if the cursor is not on a known symbol,
/// and `Err(message)` for invalid names or unsupported rename targets (imported members).
pub(crate) fn rename(
    state: &ServerState,
    uri: Uri,
    position: Position,
    new_name: String,
) -> Result<Option<WorkspaceEdit>, String> {
    if !is_valid_identifier(&new_name) {
        return Err(format!("invalid identifier: {:?}", new_name));
    }
    let Some(path) = uri_to_path(&uri) else {
        return Ok(None);
    };
    let mut fallback = None;
    let Some(graph) = resolve_graph(state, &uri, &mut fallback) else {
        return Ok(None);
    };
    let Some((_, program)) = graph.module_for_path(&path) else {
        return Ok(None);
    };
    let index = index_program(program);
    let position = SourcePosition {
        line: position.line as usize + 1,
        col: position.character as usize + 1,
    };
    let Some(target) = rename_target_at(&index, position)? else {
        return Ok(None);
    };
    if target.spans.is_empty() {
        return Ok(None);
    }
    let edits: Vec<TextEdit> = target
        .spans
        .into_iter()
        .map(|span| TextEdit {
            range: source_span_to_range(span),
            new_text: new_name.clone(),
        })
        .collect();
    let mut changes = HashMap::new();
    changes.insert(uri, edits);
    Ok(Some(WorkspaceEdit {
        changes: Some(changes),
        ..Default::default()
    }))
}
