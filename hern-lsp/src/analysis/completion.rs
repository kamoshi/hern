use super::hover::{completion_scheme_to_string, completion_ty_to_display_string};
use super::state::{ServerState, cached_analysis};
use super::uri::uri_to_path;
use super::workspace::{
    WorkspaceAnalysis, analyze_document_graph, load_document_graph_recovering,
    load_workspace_graphs,
};
use hern_core::ast::{Program, SourcePosition};
use hern_core::module::{GraphInference, ModuleGraph, infer_graph_collecting};
use hern_core::source_index::{
    CompletionCandidate, Definition, DefinitionKind, SourceIndex, index_program,
};
use hern_core::types::Ty;
use hern_core::types::infer::TypeEnv;
use lsp_types::{
    CompletionItem, CompletionItemKind, CompletionItemLabelDetails, CompletionTextEdit, Position,
    Range, TextEdit, Uri,
};
use std::collections::HashMap;
use std::fs;

/// Acquires the module graph and inference for completion, trying four strategies
/// in order: cached analysis, full re-analysis, partial analysis (type errors ok),
/// parse-only recovery with empty inference.
fn acquire_completion_graphs(state: &ServerState, uri: &Uri) -> Option<WorkspaceAnalysis> {
    if let Ok(wa) = analyze_document_graph(state, uri) {
        return Some(wa);
    }
    // Partial: graph loaded but type errors prevented full inference.
    if let Some(wa) = load_workspace_graphs(state, uri) {
        return Some(wa);
    }
    // Parse-only: syntax errors but we can still suggest names from scope.
    let mut graph = load_document_graph_recovering(state, uri)?;
    let inference = infer_graph_collecting(&mut graph).value.unwrap_or_default();
    Some(WorkspaceAnalysis { graph, inference })
}

pub(crate) fn completion(state: &ServerState, uri: Uri, position: Position) -> Vec<CompletionItem> {
    state.timed("completion", || completion_inner(state, uri, position))
}

fn completion_inner(state: &ServerState, uri: Uri, position: Position) -> Vec<CompletionItem> {
    let Some(path) = uri_to_path(&uri) else {
        return Vec::new();
    };

    if let Some(items) = import_path_completion(state, &uri, position) {
        return items;
    }

    let owned;
    let (graph, inference): (&ModuleGraph, &GraphInference) =
        if let Some(cached) = cached_analysis(state, &uri) {
            (&cached.graph, &cached.inference)
        } else {
            let Some(wa) = acquire_completion_graphs(state, &uri) else {
                return Vec::new();
            };
            owned = wa;
            (&owned.graph, &owned.inference)
        };

    let Some((module_name, program)) = graph.module_for_path(&path) else {
        return Vec::new();
    };

    let lsp_position = position;
    let position = SourcePosition {
        line: lsp_position.line as usize + 1,
        col: lsp_position.character as usize + 1,
    };

    let index = state.timed("source indexing", || index_program(program));
    let prelude_index = state.timed("prelude source indexing", || index_program(&graph.prelude));
    if is_binding_declaration_position(state, &uri, lsp_position) {
        return Vec::new();
    }
    let candidates = visible_completion_candidates(&index, &prelude_index, position);
    let env = inference.env_for_module(module_name);
    let binding_types = inference.binding_types_for_module(module_name);
    let definition_schemes = inference.definition_schemes_for_module(module_name);
    let replacement_range = completion_replacement_range(state, &uri, lsp_position);

    if let Some(items) = member_completion(
        state,
        &uri,
        graph,
        inference,
        module_name,
        &index,
        &prelude_index,
        position,
        lsp_position,
    ) {
        return items;
    }

    if let Some(items) = type_position_completion(
        state,
        &uri,
        &index,
        &prelude_index,
        lsp_position,
        replacement_range,
    ) {
        return items;
    }

    use hern_core::source_index::CompletionCandidateKind;
    candidates
        .into_iter()
        .map(|candidate| {
            let detail = completion_detail(
                &index,
                &prelude_index,
                &candidate.name,
                position,
                env,
                binding_types,
                definition_schemes,
            );
            let kind = Some(match candidate.kind {
                CompletionCandidateKind::Function => CompletionItemKind::FUNCTION,
                CompletionCandidateKind::ImportBinding => CompletionItemKind::MODULE,
                _ => CompletionItemKind::VARIABLE,
            });
            CompletionItem {
                label: candidate.name.clone(),
                kind,
                filter_text: Some(candidate.name.clone()),
                insert_text: Some(candidate.name.clone()),
                text_edit: replacement_range.map(|range| {
                    CompletionTextEdit::Edit(TextEdit {
                        range,
                        new_text: candidate.name.clone(),
                    })
                }),
                label_details: detail.as_ref().map(|detail| CompletionItemLabelDetails {
                    detail: Some(format!(": {detail}")),
                    description: None,
                }),
                detail,
                ..Default::default()
            }
        })
        .collect()
}

fn import_path_completion(
    state: &ServerState,
    uri: &Uri,
    position: Position,
) -> Option<Vec<CompletionItem>> {
    let source = state.documents.get(uri)?;
    let line = source.lines().nth(position.line as usize)?;
    let cursor_byte = utf16_col_to_byte(line, position.character).min(line.len());
    let before = &line[..cursor_byte];
    let quote = before.rfind('"')?;
    if before[..quote].contains('"') || !before[..quote].contains("import") {
        return None;
    }
    let prefix = &before[quote + 1..];
    let doc_path = uri_to_path(uri)?;
    let doc_dir = doc_path.parent()?;
    let (dir_part, name_prefix) = match prefix.rfind('/') {
        Some(idx) => (&prefix[..=idx], &prefix[idx + 1..]),
        None => ("", prefix),
    };
    let search_dir = doc_dir.join(dir_part);
    if !state.path_is_in_workspace(&search_dir) {
        return Some(Vec::new());
    }
    let entries = fs::read_dir(search_dir).ok()?;
    let replace_range = Range::new(
        Position::new(position.line, byte_to_utf16_col(line, quote + 1)),
        position,
    );
    let mut items = Vec::new();
    for entry in entries.flatten() {
        let path = entry.path();
        let Some(file_name) = path.file_name().and_then(|name| name.to_str()) else {
            continue;
        };
        if path.is_dir() {
            if !file_name.starts_with(name_prefix) {
                continue;
            }
            let label = format!("{dir_part}{file_name}/");
            items.push(path_completion_item(
                label,
                "directory",
                CompletionItemKind::FOLDER,
                replace_range,
            ));
        } else if let Some(stem) = file_name.strip_suffix(".hern") {
            if !stem.starts_with(name_prefix) {
                continue;
            }
            let label = format!("{dir_part}{stem}");
            items.push(path_completion_item(
                label,
                "local module",
                CompletionItemKind::FILE,
                replace_range,
            ));
        }
    }
    items.sort_by(|a, b| a.label.cmp(&b.label));
    Some(items)
}

fn path_completion_item(
    label: String,
    detail: &str,
    kind: CompletionItemKind,
    range: Range,
) -> CompletionItem {
    CompletionItem {
        label: label.clone(),
        kind: Some(kind),
        filter_text: Some(label.clone()),
        insert_text: Some(label.clone()),
        text_edit: Some(CompletionTextEdit::Edit(TextEdit {
            range,
            new_text: label,
        })),
        detail: Some(detail.to_string()),
        ..Default::default()
    }
}

fn member_completion(
    state: &ServerState,
    uri: &Uri,
    graph: &ModuleGraph,
    inference: &GraphInference,
    current_module: &str,
    index: &SourceIndex,
    prelude_index: &SourceIndex,
    position: SourcePosition,
    lsp_position: Position,
) -> Option<Vec<CompletionItem>> {
    let source = state.documents.get(uri)?;
    let line = source.lines().nth(lsp_position.line as usize)?;
    let cursor_byte = utf16_col_to_byte(line, lsp_position.character).min(line.len());
    let before = &line[..cursor_byte];
    let partial_start = before
        .rfind(|c: char| !is_completion_identifier_char(c))
        .map(|idx| idx + 1)
        .unwrap_or(0);
    if partial_start == 0 || before.as_bytes().get(partial_start - 1) != Some(&b'.') {
        return None;
    }
    let before_dot = &before[..partial_start - 1];
    let receiver_start = before_dot
        .rfind(|c: char| !is_completion_identifier_char(c))
        .map(|idx| idx + 1)
        .unwrap_or(0);
    let receiver = &before_dot[receiver_start..];
    if receiver.is_empty() {
        return None;
    }
    let definition = visible_definition_named(index, receiver, position)
        .or_else(|| visible_definition_named(prelude_index, receiver, position))?;
    let replacement_range = completion_replacement_range(state, uri, lsp_position)?;
    let items = if let Some(module_name) = definition.import_module.as_ref() {
        imported_member_completion_items(graph, inference, module_name, replacement_range)
    } else if let Some(ty) = completion_type_for_definition(inference, current_module, definition) {
        record_field_completion_items(&ty, replacement_range)
    } else {
        Vec::new()
    };
    (!items.is_empty()).then_some(items)
}

fn imported_member_completion_items(
    graph: &ModuleGraph,
    inference: &GraphInference,
    module_name: &str,
    replacement_range: Range,
) -> Vec<CompletionItem> {
    let mut items = Vec::new();
    if let Some(Ty::Record(row)) = inference.import_types.get(module_name) {
        for (name, ty) in &row.fields {
            items.push(CompletionItem {
                label: name.clone(),
                kind: Some(CompletionItemKind::FIELD),
                filter_text: Some(name.clone()),
                insert_text: Some(name.clone()),
                text_edit: Some(CompletionTextEdit::Edit(TextEdit {
                    range: replacement_range,
                    new_text: name.clone(),
                })),
                detail: Some(completion_ty_to_display_string(ty)),
                ..Default::default()
            });
        }
    } else if let Some(program) = graph.module(module_name) {
        if let Some(fields) = exported_record_fields(program) {
            for name in fields {
                items.push(CompletionItem {
                    label: name.clone(),
                    kind: Some(CompletionItemKind::FIELD),
                    filter_text: Some(name.clone()),
                    insert_text: Some(name.clone()),
                    text_edit: Some(CompletionTextEdit::Edit(TextEdit {
                        range: replacement_range,
                        new_text: name,
                    })),
                    ..Default::default()
                });
            }
            items.sort_by(|a, b| a.label.cmp(&b.label));
            items.dedup_by(|a, b| a.label == b.label);
            return items;
        }
        let target_index = index_program(program);
        for definition in target_index.definitions {
            if !matches!(
                definition.kind,
                DefinitionKind::Function | DefinitionKind::Let | DefinitionKind::Extern
            ) {
                continue;
            }
            items.push(CompletionItem {
                label: definition.name.clone(),
                kind: Some(match definition.kind {
                    DefinitionKind::Function | DefinitionKind::Extern => {
                        CompletionItemKind::FUNCTION
                    }
                    _ => CompletionItemKind::VARIABLE,
                }),
                filter_text: Some(definition.name.clone()),
                insert_text: Some(definition.name.clone()),
                text_edit: Some(CompletionTextEdit::Edit(TextEdit {
                    range: replacement_range,
                    new_text: definition.name,
                })),
                ..Default::default()
            });
        }
    }
    items.sort_by(|a, b| a.label.cmp(&b.label));
    items.dedup_by(|a, b| a.label == b.label);
    items
}

fn record_field_completion_items(ty: &Ty, replacement_range: Range) -> Vec<CompletionItem> {
    let ty = match ty {
        Ty::Qualified(_, inner) => inner.as_ref(),
        other => other,
    };
    let Ty::Record(row) = ty else {
        return Vec::new();
    };
    let mut items = row
        .fields
        .iter()
        .map(|(name, ty)| CompletionItem {
            label: name.clone(),
            kind: Some(CompletionItemKind::FIELD),
            filter_text: Some(name.clone()),
            insert_text: Some(name.clone()),
            text_edit: Some(CompletionTextEdit::Edit(TextEdit {
                range: replacement_range,
                new_text: name.clone(),
            })),
            detail: Some(completion_ty_to_display_string(ty)),
            ..Default::default()
        })
        .collect::<Vec<_>>();
    items.sort_by(|a, b| a.label.cmp(&b.label));
    items
}

fn type_position_completion(
    state: &ServerState,
    uri: &Uri,
    index: &SourceIndex,
    prelude_index: &SourceIndex,
    position: Position,
    replacement_range: Option<Range>,
) -> Option<Vec<CompletionItem>> {
    if !is_type_position(state, uri, position) {
        return None;
    }
    let current_type_names = index
        .definitions
        .iter()
        .filter(|definition| is_type_completion_kind(definition.kind))
        .map(|definition| definition.name.clone())
        .collect::<std::collections::HashSet<_>>();
    let mut items = index
        .definitions
        .iter()
        .chain(
            prelude_index
                .definitions
                .iter()
                .filter(|definition| !current_type_names.contains(&definition.name)),
        )
        .filter(|definition| is_type_completion_kind(definition.kind))
        .map(|definition| {
            let kind = match definition.kind {
                DefinitionKind::Trait => CompletionItemKind::INTERFACE,
                _ => CompletionItemKind::STRUCT,
            };
            CompletionItem {
                label: definition.name.clone(),
                kind: Some(kind),
                filter_text: Some(definition.name.clone()),
                insert_text: Some(definition.name.clone()),
                text_edit: replacement_range.map(|range| {
                    CompletionTextEdit::Edit(TextEdit {
                        range,
                        new_text: definition.name.clone(),
                    })
                }),
                ..Default::default()
            }
        })
        .collect::<Vec<_>>();
    items.sort_by(|a, b| a.label.cmp(&b.label));
    items.dedup_by(|a, b| a.label == b.label);
    Some(items)
}

fn is_type_completion_kind(kind: DefinitionKind) -> bool {
    matches!(
        kind,
        DefinitionKind::Type | DefinitionKind::TypeAlias | DefinitionKind::Trait
    )
}

fn is_binding_declaration_position(state: &ServerState, uri: &Uri, position: Position) -> bool {
    let Some(line) = state
        .documents
        .get(uri)
        .and_then(|source| source.lines().nth(position.line as usize))
    else {
        return false;
    };
    let cursor_byte = utf16_col_to_byte(line, position.character).min(line.len());
    let before = line[..cursor_byte].trim_end();
    before.ends_with("let") || before.ends_with("let mut")
}

fn is_type_position(state: &ServerState, uri: &Uri, position: Position) -> bool {
    let Some(line) = state
        .documents
        .get(uri)
        .and_then(|source| source.lines().nth(position.line as usize))
    else {
        return false;
    };
    let cursor_byte = utf16_col_to_byte(line, position.character).min(line.len());
    let before = &line[..cursor_byte];
    let Some(colon) = before.rfind(':') else {
        return false;
    };
    !before[colon + 1..].contains('=')
        && !before[colon + 1..].contains('{')
        && !before[colon + 1..].contains('}')
}

fn completion_type_for_definition(
    inference: &GraphInference,
    current_module: &str,
    definition: &Definition,
) -> Option<Ty> {
    if let Some(module_name) = definition.import_module.as_ref() {
        return inference.import_types.get(module_name).cloned();
    }
    inference
        .definition_schemes_for_module(current_module)
        .and_then(|schemes| schemes.get(&definition.location.span))
        .map(|scheme| scheme.ty.clone())
        .or_else(|| {
            inference
                .binding_types_for_module(current_module)
                .and_then(|types| types.get(&definition.location.span))
                .cloned()
        })
        .or_else(|| {
            inference
                .env_for_module(current_module)
                .and_then(|env| env.get(&definition.name))
                .map(|info| info.scheme.ty.clone())
        })
}

fn exported_record_fields(program: &Program) -> Option<Vec<String>> {
    use hern_core::ast::{ExprKind, Stmt};
    let Some(Stmt::Expr(expr)) = program.stmts.last() else {
        return None;
    };
    let ExprKind::Record(fields) = &expr.kind else {
        return None;
    };
    Some(fields.iter().map(|(name, _)| name.clone()).collect())
}

fn completion_replacement_range(
    state: &ServerState,
    uri: &Uri,
    position: Position,
) -> Option<Range> {
    let line = state
        .documents
        .get(uri)?
        .lines()
        .nth(position.line as usize)?;
    let cursor_byte = utf16_col_to_byte(line, position.character);
    let start_byte = line[..cursor_byte.min(line.len())]
        .rfind(|c: char| !is_completion_identifier_char(c))
        .map(|idx| idx + 1)
        .unwrap_or(0);
    Some(Range::new(
        Position::new(position.line, byte_to_utf16_col(line, start_byte)),
        position,
    ))
}

fn is_completion_identifier_char(c: char) -> bool {
    c.is_ascii_alphanumeric() || c == '_'
}

fn utf16_col_to_byte(line: &str, col: u32) -> usize {
    let mut utf16 = 0u32;
    for (byte_idx, ch) in line.char_indices() {
        if utf16 >= col {
            return byte_idx;
        }
        utf16 += ch.len_utf16() as u32;
        if utf16 > col {
            return byte_idx;
        }
    }
    line.len()
}

fn byte_to_utf16_col(line: &str, byte: usize) -> u32 {
    line[..byte.min(line.len())]
        .chars()
        .map(|ch| ch.len_utf16() as u32)
        .sum()
}

fn completion_detail(
    index: &SourceIndex,
    prelude_index: &SourceIndex,
    name: &str,
    position: SourcePosition,
    env: Option<&TypeEnv>,
    binding_types: Option<&HashMap<hern_core::ast::SourceSpan, Ty>>,
    definition_schemes: Option<&HashMap<hern_core::ast::SourceSpan, hern_core::types::Scheme>>,
) -> Option<String> {
    let definition = visible_definition_named(index, name, position)
        .or_else(|| visible_definition_named(prelude_index, name, position));
    if let Some(definition) = definition {
        if let Some(scheme) =
            definition_schemes.and_then(|schemes| schemes.get(&definition.location.span))
        {
            return Some(completion_scheme_to_string(scheme));
        }
        if matches!(
            definition.kind,
            DefinitionKind::Let | DefinitionKind::Parameter
        ) && let Some(ty) = binding_types.and_then(|types| types.get(&definition.location.span))
        {
            return Some(completion_ty_to_display_string(ty));
        }
    }

    env.and_then(|e| e.get(name))
        .map(|info| completion_scheme_to_string(&info.scheme))
}

fn visible_completion_candidates(
    index: &SourceIndex,
    prelude_index: &SourceIndex,
    position: SourcePosition,
) -> Vec<CompletionCandidate> {
    let mut candidates = index.visible_names_at(position);
    let local_names = candidates
        .iter()
        .map(|candidate| candidate.name.clone())
        .collect::<std::collections::HashSet<_>>();

    candidates.extend(
        prelude_index
            .visible_names_at(position)
            .into_iter()
            .filter(|candidate| !candidate.name.starts_with("__"))
            .filter(|candidate| !local_names.contains(&candidate.name)),
    );
    candidates.sort_by(|a, b| a.name.cmp(&b.name));
    candidates
}

fn visible_definition_named<'a>(
    index: &'a hern_core::source_index::SourceIndex,
    name: &str,
    position: SourcePosition,
) -> Option<&'a Definition> {
    let mut best = None;
    for definition in index
        .definitions
        .iter()
        .filter(|definition| definition.name == name)
    {
        if !matches!(
            definition.kind,
            DefinitionKind::Function
                | DefinitionKind::Let
                | DefinitionKind::Parameter
                | DefinitionKind::Extern
        ) {
            continue;
        }
        let visible = definition.visibility_end.line == usize::MAX || {
            let start = (
                definition.visibility_start.line,
                definition.visibility_start.col,
            );
            let end = (
                definition.visibility_end.line,
                definition.visibility_end.col,
            );
            let cursor = (position.line, position.col);
            cursor >= start && cursor < end
        };
        if visible {
            best = Some(definition);
        }
    }
    best
}
