use super::hover::{
    ast_type_to_string, completion_scheme_to_string, completion_ty_to_display_string,
};
use super::state::{ServerState, cached_analysis, document_overlays};
use super::uri::uri_to_path;
use super::workspace::{
    WorkspaceAnalysis, analyze_document_graph, load_document_graph_recovering,
    load_workspace_graphs,
};
use hern_core::ast::{
    Expr, ExprKind, NodeId, Program, RecordEntry, SourcePosition, SourceSpan, Stmt, TraitDef,
};
use hern_core::module::{
    GraphInference, ModuleGraph, infer_graph_collecting, normalize_overlay_path,
};
use hern_core::source_index::{
    CompletionCandidate, Definition, DefinitionKind, SourceIndex, index_program,
};
use hern_core::types::infer::TypeEnv;
use hern_core::types::{ParamCapability, Scheme, Ty, inherent_impl_target_keys_from_ty};
use lsp_types::{
    CompletionItem, CompletionItemKind, CompletionItemLabelDetails, CompletionTextEdit, Position,
    Range, TextEdit, Uri,
};
use std::collections::HashMap;
use std::fs;

/// Acquires the module graph and inference for completion, trying four strategies
/// in order: cached analysis, full re-analysis, partial analysis (type errors ok),
/// parse-only recovery with empty inference.
fn acquire_completion_graphs(
    state: &ServerState,
    uri: &Uri,
    recovery_source: Option<String>,
) -> Option<WorkspaceAnalysis> {
    if let Some(source) = recovery_source
        && let Some(wa) = analyze_completion_recovery_source(state, uri, source)
    {
        return Some(wa);
    }
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

fn analyze_completion_recovery_source(
    state: &ServerState,
    uri: &Uri,
    source: String,
) -> Option<WorkspaceAnalysis> {
    let path = uri_to_path(uri)?;
    let mut overlays = document_overlays(state);
    overlays.insert(normalize_overlay_path(&path), source);
    let (mut graph, _) = ModuleGraph::load_entry_with_prelude_and_overlays(
        &path,
        state.prelude.program.clone(),
        overlays,
    )
    .ok()?;
    let inference = infer_graph_collecting(&mut graph).value?;
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

    let recovery_source = member_completion_recovery_source(state, &uri, position);
    let owned;
    let (graph, inference): (&ModuleGraph, &GraphInference) = if recovery_source.is_none()
        && let Some(cached) = cached_analysis(state, &uri)
    {
        (&cached.graph, &cached.inference)
    } else {
        let Some(wa) = acquire_completion_graphs(state, &uri, recovery_source) else {
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

    if let Some(items) = associated_completion(state, &uri, inference, module_name, lsp_position) {
        return items;
    }

    if let Some(items) = member_completion(
        state,
        &uri,
        graph,
        inference,
        module_name,
        program,
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
    let mut items: Vec<CompletionItem> = candidates
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
        .collect();

    // Add trait names from the module environment. Traits are used in value position
    // as `TraitName::method(...)`, so they belong in the default completion list.
    if let Some(module_env) = inference.module_env_for_module(module_name) {
        let trait_items = {
            let existing: std::collections::HashSet<&str> =
                items.iter().map(|i| i.label.as_str()).collect();
            module_env
                .all_trait_defs()
                .filter(|(trait_name, _)| {
                    !is_internal_completion_name(trait_name) && !existing.contains(trait_name)
                })
                .map(|(trait_name, trait_def)| {
                    let detail = Some(format!(
                        "trait {} {}",
                        trait_name,
                        trait_def.params.join(" ")
                    ));
                    CompletionItem {
                        label: trait_name.to_string(),
                        kind: Some(CompletionItemKind::INTERFACE),
                        detail: detail.clone(),
                        filter_text: Some(trait_name.to_string()),
                        insert_text: Some(trait_name.to_string()),
                        text_edit: replacement_range.map(|range| {
                            CompletionTextEdit::Edit(TextEdit {
                                range,
                                new_text: trait_name.to_string(),
                            })
                        }),
                        label_details: detail.map(|d| CompletionItemLabelDetails {
                            detail: Some(format!(": {d}")),
                            description: None,
                        }),
                        ..Default::default()
                    }
                })
                .collect::<Vec<_>>()
        };
        items.extend(trait_items);
        items.sort_by(|a, b| a.label.cmp(&b.label));
    }

    items
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

struct MemberCompletionContext {
    receiver: Option<String>,
    receiver_end: SourcePosition,
    replacement_range: Range,
}

struct AssociatedCompletionContext {
    target: String,
    replacement_range: Range,
}

fn member_completion_context(
    state: &ServerState,
    uri: &Uri,
    lsp_position: Position,
) -> Option<MemberCompletionContext> {
    let source = state.documents.get(uri)?;
    let cursor_byte = position_to_byte(source, lsp_position)?;
    let (dot_byte, partial_start, replacement_end) = member_access_bounds(source, cursor_byte)?;
    let receiver_end_byte = source[..dot_byte].trim_end().len();
    if receiver_end_byte == 0 {
        return None;
    }
    let receiver_start = source[..receiver_end_byte]
        .rfind(|c: char| !is_completion_identifier_char(c))
        .map(|idx| idx + 1)
        .unwrap_or(0);
    let receiver = &source[receiver_start..receiver_end_byte];
    let receiver = (!receiver.is_empty() && receiver.chars().all(is_completion_identifier_char))
        .then(|| receiver.to_string());
    Some(MemberCompletionContext {
        receiver,
        receiver_end: byte_to_source_position(source, receiver_end_byte),
        replacement_range: Range::new(
            byte_to_lsp_position(source, partial_start),
            byte_to_lsp_position(source, replacement_end),
        ),
    })
}

fn member_completion_recovery_source(
    state: &ServerState,
    uri: &Uri,
    lsp_position: Position,
) -> Option<String> {
    let source = state.documents.get(uri)?;
    let cursor_byte = position_to_byte(source, lsp_position)?;
    let (dot_byte, _, _) = member_access_bounds(source, cursor_byte)?;
    let mut recovered = source[..dot_byte].to_string();
    // First terminate the partial member-access statement, then balance any
    // delimiters that statement sits inside, then terminate again in case the
    // inserted closers completed an expression instead of a statement.
    terminate_completion_recovery_statement(&mut recovered);
    close_unmatched_braces_for_completion(&mut recovered);
    terminate_completion_recovery_statement(&mut recovered);
    Some(recovered)
}

fn terminate_completion_recovery_statement(source: &mut String) {
    let trimmed = source.trim_end();
    if trimmed.is_empty()
        || trimmed.ends_with(';')
        || trimmed.ends_with('{')
        || trimmed.ends_with('}')
        || trimmed.ends_with(',')
    {
        return;
    }
    source.push(';');
}

fn close_unmatched_braces_for_completion(source: &mut String) {
    let mut open_delimiters = Vec::new();
    let mut in_string = false;
    let mut chars = source.chars().peekable();
    while let Some(ch) = chars.next() {
        match ch {
            '"' => in_string = !in_string,
            '\\' if in_string => {
                chars.next();
            }
            '/' if !in_string && chars.peek() == Some(&'/') => {
                for ch in chars.by_ref() {
                    if ch == '\n' {
                        break;
                    }
                }
            }
            '(' | '{' | '[' if !in_string => open_delimiters.push(ch),
            ')' if !in_string => close_delimiter(&mut open_delimiters, '('),
            '}' if !in_string => close_delimiter(&mut open_delimiters, '{'),
            ']' if !in_string => close_delimiter(&mut open_delimiters, '['),
            _ => {}
        }
    }
    for opener in open_delimiters.into_iter().rev() {
        source.push(match opener {
            '(' => ')',
            '{' => '}',
            '[' => ']',
            _ => unreachable!("only tracked delimiters are stored"),
        });
    }
}

fn close_delimiter(open_delimiters: &mut Vec<char>, opener: char) {
    if open_delimiters.last() == Some(&opener) {
        open_delimiters.pop();
    } else if let Some(pos) = open_delimiters.iter().rposition(|ch| *ch == opener) {
        // Completion recovery should salvage as much prefix context as possible.
        // If the user has mismatched delimiters before the cursor, remove the
        // nearest matching opener and leave newer openers to be closed below.
        open_delimiters.remove(pos);
    }
}

fn line_byte_range(source: &str, target_line: usize) -> Option<(usize, usize)> {
    let mut line = 0usize;
    let mut start = 0usize;
    for (idx, ch) in source.char_indices() {
        if line == target_line && ch == '\n' {
            return Some((start, idx));
        }
        if ch == '\n' {
            line += 1;
            start = idx + ch.len_utf8();
        }
    }
    (line == target_line).then_some((start, source.len()))
}

fn position_to_byte(source: &str, position: Position) -> Option<usize> {
    let (line_start, line_end) = line_byte_range(source, position.line as usize)?;
    let line = &source[line_start..line_end];
    Some(line_start + utf16_col_to_byte(line, position.character).min(line.len()))
}

fn byte_to_lsp_position(source: &str, byte: usize) -> Position {
    let byte = byte.min(source.len());
    let mut line = 0u32;
    let mut line_start = 0usize;
    for (idx, ch) in source.char_indices() {
        if idx >= byte {
            break;
        }
        if ch == '\n' {
            line += 1;
            line_start = idx + ch.len_utf8();
        }
    }
    let line_end = source[line_start..]
        .find('\n')
        .map(|offset| line_start + offset)
        .unwrap_or(source.len());
    Position::new(
        line,
        byte_to_utf16_col(&source[line_start..line_end], byte - line_start),
    )
}

fn byte_to_source_position(source: &str, byte: usize) -> SourcePosition {
    let position = byte_to_lsp_position(source, byte);
    SourcePosition {
        line: position.line as usize + 1,
        col: position.character as usize + 1,
    }
}

fn member_access_bounds(source: &str, cursor_byte: usize) -> Option<(usize, usize, usize)> {
    let cursor_byte = cursor_byte.min(source.len());
    let before = &source[..cursor_byte];
    let partial_start = before
        .rfind(|c: char| !is_completion_identifier_char(c))
        .map(|idx| idx + 1)
        .unwrap_or(0);
    if partial_start > 0 && before.as_bytes().get(partial_start - 1) == Some(&b'.') {
        return Some((partial_start - 1, partial_start, cursor_byte));
    }
    if source.as_bytes().get(cursor_byte) == Some(&b'.') {
        return Some((cursor_byte, cursor_byte + 1, cursor_byte + 1));
    }
    None
}

fn associated_completion_context(
    state: &ServerState,
    uri: &Uri,
    lsp_position: Position,
) -> Option<AssociatedCompletionContext> {
    let source = state.documents.get(uri)?;
    let line = source.lines().nth(lsp_position.line as usize)?;
    let cursor_byte = utf16_col_to_byte(line, lsp_position.character).min(line.len());
    let (colon_start, member_start, replacement_end) = associated_access_bounds(line, cursor_byte)?;
    let target_end = colon_start;
    let target_start = line[..target_end]
        .rfind(|c: char| !is_completion_identifier_char(c))
        .map(|idx| idx + 1)
        .unwrap_or(0);
    let target = &line[target_start..target_end];
    if target.is_empty() {
        return None;
    }
    Some(AssociatedCompletionContext {
        target: target.to_string(),
        replacement_range: Range::new(
            Position::new(lsp_position.line, byte_to_utf16_col(line, member_start)),
            Position::new(lsp_position.line, byte_to_utf16_col(line, replacement_end)),
        ),
    })
}

fn associated_access_bounds(line: &str, cursor_byte: usize) -> Option<(usize, usize, usize)> {
    let cursor_byte = cursor_byte.min(line.len());
    let before = &line[..cursor_byte];
    if let Some(colon_start) = before.rfind("::") {
        let member_start = colon_start + 2;
        let partial = &before[member_start..];
        if partial.chars().all(is_completion_identifier_char) {
            return Some((colon_start, member_start, cursor_byte));
        }
    }
    if cursor_byte > 0
        && line.as_bytes().get(cursor_byte - 1) == Some(&b':')
        && line.as_bytes().get(cursor_byte) == Some(&b':')
    {
        return Some((cursor_byte - 1, cursor_byte + 1, cursor_byte + 1));
    }
    if cursor_byte + 1 < line.len()
        && line.as_bytes().get(cursor_byte) == Some(&b':')
        && line.as_bytes().get(cursor_byte + 1) == Some(&b':')
    {
        return Some((cursor_byte, cursor_byte + 2, cursor_byte + 2));
    }
    None
}

#[allow(clippy::too_many_arguments)]
fn member_completion(
    state: &ServerState,
    uri: &Uri,
    graph: &ModuleGraph,
    inference: &GraphInference,
    current_module: &str,
    program: &Program,
    index: &SourceIndex,
    prelude_index: &SourceIndex,
    position: SourcePosition,
    lsp_position: Position,
) -> Option<Vec<CompletionItem>> {
    let context = member_completion_context(state, uri, lsp_position)?;
    let replacement_range = context.replacement_range;

    // Definition-based completions: import module members and record fields.
    if let Some(receiver) = context.receiver.as_deref()
        && let Some(definition) = visible_definition_named(index, receiver, position)
            .or_else(|| visible_definition_named(prelude_index, receiver, position))
    {
        if let Some(mod_name) = definition.import_module.as_ref() {
            let items =
                imported_member_completion_items(graph, inference, mod_name, replacement_range);
            if !items.is_empty() {
                return Some(items);
            }
        }

        if let Some(ty) = completion_type_for_definition(inference, current_module, definition) {
            let mut items = record_field_completion_items(&ty, replacement_range);
            let receiver_place_mutable =
                completion_place_mutable_for_definition(inference, current_module, definition);
            items.extend(receiver_method_completion_items(
                inference,
                current_module,
                &ty,
                receiver_place_mutable,
                replacement_range,
            ));
            items.sort_by(|a, b| a.label.cmp(&b.label));
            items.dedup_by(|a, b| a.label == b.label);
            if !items.is_empty() {
                return Some(items);
            }
        }
    }

    if let Some((receiver_id, receiver_span, ty)) =
        completion_type_for_receiver_expr(program, inference, current_module, context.receiver_end)
    {
        let mut items = record_field_completion_items(&ty, replacement_range);
        let receiver_place_mutable = inference
            .fresh_place_exprs_for_module(current_module)
            .is_some_and(|fresh| fresh.contains(&receiver_id))
            || inference
                .binding_capabilities_for_module(current_module)
                .and_then(|caps| caps.get(&receiver_span))
                .is_some_and(|caps| caps.place_mutable);
        items.extend(receiver_method_completion_items(
            inference,
            current_module,
            &ty,
            receiver_place_mutable,
            replacement_range,
        ));
        items.sort_by(|a, b| a.label.cmp(&b.label));
        items.dedup_by(|a, b| a.label == b.label);
        if !items.is_empty() {
            return Some(items);
        }
    }

    Some(Vec::new())
}

fn associated_completion(
    state: &ServerState,
    uri: &Uri,
    inference: &GraphInference,
    current_module: &str,
    lsp_position: Position,
) -> Option<Vec<CompletionItem>> {
    let context = associated_completion_context(state, uri, lsp_position)?;
    let target = context.target.as_str();
    let replacement_range = context.replacement_range;
    let mut items = Vec::new();
    if let Some(module_env) = inference.module_env_for_module(current_module) {
        if let Some(trait_def) = module_env.trait_def(target) {
            items.extend(trait_method_completion_items(trait_def, replacement_range));
        }
        for (method_target, methods) in module_env.all_inherent_methods() {
            if method_target == target {
                items.extend(associated_method_completion_items(
                    methods,
                    replacement_range,
                ));
            }
        }
    }
    if items.is_empty()
        && let Some(methods) = state.prelude.inherent_method_schemes.get(target)
    {
        items.extend(associated_method_completion_items(
            methods,
            replacement_range,
        ));
    }
    if items.is_empty()
        && let Some(trait_def) = prelude_trait_def(&state.prelude.program, target)
    {
        items.extend(trait_method_completion_items(trait_def, replacement_range));
    }
    items.sort_by(|a, b| a.label.cmp(&b.label));
    items.dedup_by(|a, b| a.label == b.label);
    // A recognized `Type::` context suppresses general scope completion even when
    // the type has no associated functions; the user explicitly requested members.
    Some(items)
}

fn prelude_trait_def<'a>(program: &'a Program, name: &str) -> Option<&'a TraitDef> {
    program.stmts.iter().find_map(|stmt| match stmt {
        Stmt::Trait(trait_def) if trait_def.name == name => Some(trait_def),
        _ => None,
    })
}

fn associated_method_completion_items(
    methods: &HashMap<String, hern_core::types::InherentMethodScheme>,
    replacement_range: Range,
) -> Vec<CompletionItem> {
    methods
        .iter()
        .filter(|(name, method)| !is_internal_completion_name(name) && !method.has_receiver)
        .map(|(name, method)| {
            method_completion_item(
                name,
                &method.scheme,
                CompletionItemKind::FUNCTION,
                replacement_range,
            )
        })
        .collect()
}

fn receiver_method_completion_items(
    inference: &GraphInference,
    current_module: &str,
    receiver_ty: &Ty,
    receiver_place_mutable: bool,
    replacement_range: Range,
) -> Vec<CompletionItem> {
    let Some(module_env) = inference.module_env_for_module(current_module) else {
        return Vec::new();
    };
    let target_keys = inherent_impl_target_keys_from_ty(receiver_ty);
    let mut seen = std::collections::HashSet::new();
    let mut items = Vec::new();
    for target in target_keys {
        for (_, methods) in module_env
            .all_inherent_methods()
            .filter(|(method_target, _)| *method_target == target)
        {
            for (name, method) in methods {
                if is_internal_completion_name(name)
                    || !method.has_receiver
                    || (!receiver_place_mutable
                        && scheme_param_capability(&method.scheme, 0).is_mut_place())
                    || !seen.insert(name.clone())
                {
                    continue;
                }
                items.push(method_completion_item(
                    name,
                    &method.scheme,
                    CompletionItemKind::METHOD,
                    replacement_range,
                ));
            }
        }
    }
    items
}

fn method_completion_item(
    name: &str,
    scheme: &Scheme,
    kind: CompletionItemKind,
    replacement_range: Range,
) -> CompletionItem {
    let detail = Some(completion_scheme_to_string(scheme));
    CompletionItem {
        label: name.to_string(),
        kind: Some(kind),
        detail: detail.clone(),
        filter_text: Some(name.to_string()),
        insert_text: Some(name.to_string()),
        text_edit: Some(CompletionTextEdit::Edit(TextEdit {
            range: replacement_range,
            new_text: name.to_string(),
        })),
        label_details: detail.map(|d| CompletionItemLabelDetails {
            detail: Some(format!(": {d}")),
            description: None,
        }),
        ..Default::default()
    }
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
            if is_internal_completion_name(name) {
                continue;
            }
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
                if is_internal_completion_name(&name) {
                    continue;
                }
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
            ) || is_internal_completion_name(&definition.name)
            {
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
        .filter(|(name, _)| !is_internal_completion_name(name))
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

fn trait_method_completion_items(
    trait_def: &TraitDef,
    replacement_range: Range,
) -> Vec<CompletionItem> {
    let mut items: Vec<CompletionItem> = trait_def
        .methods
        .iter()
        .filter(|method| !is_internal_completion_name(&method.name))
        .map(|method| {
            let params = method
                .params
                .iter()
                .map(|(name, ty)| format!("{name}: {}", ast_type_to_string(ty)))
                .collect::<Vec<_>>()
                .join(", ");
            let detail = Some(format!(
                "fn({}) -> {}",
                params,
                ast_type_to_string(&method.ret_type)
            ));
            CompletionItem {
                label: method.name.clone(),
                kind: Some(CompletionItemKind::METHOD),
                detail: detail.clone(),
                filter_text: Some(method.name.clone()),
                insert_text: Some(method.name.clone()),
                text_edit: Some(CompletionTextEdit::Edit(TextEdit {
                    range: replacement_range,
                    new_text: method.name.clone(),
                })),
                label_details: detail.map(|d| CompletionItemLabelDetails {
                    detail: Some(format!(": {d}")),
                    description: None,
                }),
                ..Default::default()
            }
        })
        .collect();
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
        .filter(|definition| !is_internal_completion_name(&definition.name))
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

fn completion_type_for_receiver_expr(
    program: &Program,
    inference: &GraphInference,
    current_module: &str,
    receiver_end: SourcePosition,
) -> Option<(NodeId, SourceSpan, Ty)> {
    let expr = find_expr_ending_at(program, receiver_end)?;
    let span = expr.span;
    inference
        .expr_types_for_module(current_module)
        .and_then(|types| types.get(&expr.id))
        .or_else(|| {
            inference
                .symbol_types_for_module(current_module)
                .and_then(|types| types.get(&expr.id))
        })
        .cloned()
        .map(|ty| (expr.id, span, ty))
}

fn find_expr_ending_at(program: &Program, end: SourcePosition) -> Option<&Expr> {
    program
        .stmts
        .iter()
        .filter_map(|stmt| find_expr_ending_at_in_stmt(stmt, end))
        .max_by_key(|expr| (expr.span.start_line, expr.span.start_col))
}

fn find_expr_ending_at_in_stmt(stmt: &hern_core::ast::Stmt, end: SourcePosition) -> Option<&Expr> {
    match stmt {
        hern_core::ast::Stmt::Let { value, .. } | hern_core::ast::Stmt::Expr(value) => {
            find_expr_ending_at_in_expr(value, end)
        }
        hern_core::ast::Stmt::Fn { body, .. } | hern_core::ast::Stmt::Op { body, .. } => {
            find_expr_ending_at_in_expr(body, end)
        }
        hern_core::ast::Stmt::Impl(def) => def
            .methods
            .iter()
            .find_map(|method| find_expr_ending_at_in_expr(&method.body, end)),
        hern_core::ast::Stmt::InherentImpl(def) => def
            .methods
            .iter()
            .find_map(|method| find_expr_ending_at_in_expr(&method.body, end)),
        hern_core::ast::Stmt::TestBlock { stmts, .. } => stmts
            .iter()
            .find_map(|stmt| find_expr_ending_at_in_stmt(stmt, end)),
        hern_core::ast::Stmt::Trait(_)
        | hern_core::ast::Stmt::Type(_)
        | hern_core::ast::Stmt::TypeAlias { .. }
        | hern_core::ast::Stmt::Extern { .. } => None,
    }
}

fn find_expr_ending_at_in_expr(expr: &Expr, end: SourcePosition) -> Option<&Expr> {
    let mut best = (expr.span.end_line == end.line && expr.span.end_col == end.col).then_some(expr);
    for child in expr_children(expr) {
        if let Some(candidate) = find_expr_ending_at_in_expr(child, end) {
            best = Some(match best {
                Some(current)
                    if (current.span.start_line, current.span.start_col)
                        <= (candidate.span.start_line, candidate.span.start_col) =>
                {
                    current
                }
                _ => candidate,
            });
        }
    }
    best
}

fn expr_children(expr: &Expr) -> Vec<&Expr> {
    match &expr.kind {
        ExprKind::Grouped(expr) | ExprKind::Not(expr) | ExprKind::Loop(expr) => vec![expr],
        ExprKind::Neg { operand, .. } => vec![operand],
        ExprKind::Assign { target, value } => vec![target, value],
        ExprKind::Binary { lhs, rhs, .. } => vec![lhs, rhs],
        ExprKind::Range { start, end, .. } => start
            .iter()
            .chain(end.iter())
            .map(|expr| expr.as_ref())
            .collect(),
        ExprKind::Call { callee, args, .. } => std::iter::once(callee.as_ref())
            .chain(args.iter())
            .collect(),
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
        } => vec![cond, then_branch, else_branch],
        ExprKind::Match { scrutinee, arms } => std::iter::once(scrutinee.as_ref())
            .chain(arms.iter().map(|(_, body)| body))
            .collect(),
        ExprKind::Break(Some(expr)) => vec![expr],
        ExprKind::Break(None) | ExprKind::Continue => Vec::new(),
        ExprKind::Return(Some(expr)) => vec![expr],
        ExprKind::Return(None) => Vec::new(),
        ExprKind::Block { stmts, final_expr } => stmts
            .iter()
            .filter_map(|stmt| first_expr_in_stmt(stmt))
            .chain(final_expr.iter().map(|expr| expr.as_ref()))
            .collect(),
        ExprKind::Tuple(items) => items.iter().collect(),
        ExprKind::Array(items) => items.iter().map(|item| item.expr()).collect(),
        ExprKind::Record(entries) => entries.iter().map(|entry| entry.expr()).collect(),
        ExprKind::FieldAccess { expr, .. } => vec![expr],
        ExprKind::Index { receiver, key, .. } => vec![receiver, key],
        ExprKind::Lambda { body, .. } => vec![body],
        ExprKind::For { iterable, body, .. } => vec![iterable, body],
        ExprKind::Number(_)
        | ExprKind::StringLit(_)
        | ExprKind::Bool(_)
        | ExprKind::Ident(_)
        | ExprKind::AssociatedAccess { .. }
        | ExprKind::Import(_)
        | ExprKind::Unit => Vec::new(),
    }
}

fn first_expr_in_stmt(stmt: &hern_core::ast::Stmt) -> Option<&Expr> {
    match stmt {
        hern_core::ast::Stmt::Let { value, .. } | hern_core::ast::Stmt::Expr(value) => Some(value),
        hern_core::ast::Stmt::Fn { body, .. } | hern_core::ast::Stmt::Op { body, .. } => Some(body),
        _ => None,
    }
}

fn exported_record_fields(program: &Program) -> Option<Vec<String>> {
    use hern_core::ast::{ExprKind, Stmt};
    let Some(Stmt::Expr(expr)) = program.stmts.last() else {
        return None;
    };
    let ExprKind::Record(entries) = &expr.kind else {
        return None;
    };
    Some(
        entries
            .iter()
            .filter_map(|e| {
                if let RecordEntry::Field(name, _) = e {
                    Some(name.clone())
                } else {
                    None
                }
            })
            .collect(),
    )
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
    let mut candidates = index
        .visible_names_at(position)
        .into_iter()
        .filter(|candidate| !is_internal_completion_name(&candidate.name))
        .collect::<Vec<_>>();
    let local_names = candidates
        .iter()
        .map(|candidate| candidate.name.clone())
        .collect::<std::collections::HashSet<_>>();

    candidates.extend(
        prelude_index
            .visible_names_at(position)
            .into_iter()
            .filter(|candidate| !is_internal_completion_name(&candidate.name))
            .filter(|candidate| !local_names.contains(&candidate.name)),
    );
    candidates.sort_by(|a, b| a.name.cmp(&b.name));
    candidates
}

fn scheme_param_capability(scheme: &Scheme, idx: usize) -> ParamCapability {
    match &scheme.ty {
        Ty::Func(params, _) => params
            .get(idx)
            .map(|param| param.capability)
            .unwrap_or(ParamCapability::Value),
        _ => ParamCapability::Value,
    }
}

fn completion_place_mutable_for_definition(
    inference: &GraphInference,
    current_module: &str,
    definition: &Definition,
) -> bool {
    inference
        .binding_capabilities_for_module(current_module)
        .and_then(|capabilities| capabilities.get(&definition.location.span))
        .is_some_and(|capabilities| capabilities.place_mutable)
        || inference
            .env_for_module(current_module)
            .and_then(|env| env.get(&definition.name))
            .is_some_and(|info| info.is_place_mutable())
}

fn is_internal_completion_name(name: &str) -> bool {
    name.starts_with("__")
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::analysis::tests::{ImportFixture, TestProject, import_fixture, source_with_cursor};

    fn labels(items: Vec<CompletionItem>) -> Vec<String> {
        items.into_iter().map(|item| item.label).collect()
    }

    #[test]
    fn associated_completion_lists_static_functions_only() {
        let project = TestProject::new("completion-associated");
        let source = "let mut g = Map::new();\ng\n";
        let (state, uri) = project.open("main.hern", source);

        let labels = labels(completion(&state, uri, Position::new(0, 17)));

        assert!(labels.iter().any(|label| label == "new"));
        assert!(!labels.iter().any(|label| label == "set"));
        assert!(!labels.iter().any(|label| label == "get"));
        assert!(!labels.iter().any(|label| label.starts_with("__")));
    }

    #[test]
    fn associated_completion_lists_static_functions_with_parameters() {
        let project = TestProject::new("completion-associated-parameterized");
        let source = concat!(
            "type Counter = Counter(float)\n",
            "impl Counter {\n",
            "  fn make(value: float) -> Self { Counter(value) }\n",
            "  fn value(self) -> float { match self { Counter(value) -> value } }\n",
            "}\n",
            "let c = Counter::\n",
        );
        let (state, uri) = project.open("main.hern", source);

        let labels = labels(completion(&state, uri, Position::new(5, 17)));

        assert!(labels.iter().any(|label| label == "make"));
        assert!(!labels.iter().any(|label| label == "value"));
    }

    #[test]
    fn associated_completion_works_on_and_after_coloncolon() {
        for (name, marked_source) in [
            ("cursor-on-trigger", "let mut g = Map:<|>:\n"),
            ("after-trigger", "let mut g = Map::<|>\n"),
        ] {
            let project = TestProject::new(&format!("completion-associated-{name}"));
            let (source, position) = source_with_cursor(marked_source);
            let (state, uri) = project.open("main.hern", &source);

            let labels = labels(completion(&state, uri, position));

            assert!(
                labels.iter().any(|label| label == "new"),
                "{name}: {labels:?}"
            );
            assert!(
                !labels.iter().any(|label| label == "set"),
                "{name}: {labels:?}"
            );
            assert!(
                !labels.iter().any(|label| label.starts_with("__")),
                "{name}: {labels:?}"
            );
        }
    }

    #[test]
    fn receiver_completion_lists_methods_for_mutable_map_place() {
        let project = TestProject::new("completion-map-mut-methods");
        let source = "let mut g = Map::new();\ng.\n";
        let (state, uri) = project.open("main.hern", source);

        let labels = labels(completion(&state, uri, Position::new(1, 2)));

        assert!(labels.iter().any(|label| label == "set"));
        assert!(labels.iter().any(|label| label == "delete"));
        assert!(labels.iter().any(|label| label == "get"));
        assert!(labels.iter().any(|label| label == "keys"));
        assert!(!labels.iter().any(|label| label == "new"));
        assert!(!labels.iter().any(|label| label.starts_with("__")));
    }

    #[test]
    fn receiver_completion_recovers_around_incomplete_dot_contexts() {
        let cases = [
            ("on-trigger", "let mut g = Map::new();\ng<|>.\n", "g"),
            (
                "inside-block",
                "fn main() {\n    let mut g = Map::new();\n    g.<|>\n}\n",
                "main",
            ),
            (
                "unclosed-function",
                "fn main() {\n    let mut g = Map::new();\n    g.<|>\n",
                "main",
            ),
            (
                "before-let",
                concat!(
                    "fn main() {\n",
                    "    let mut g = Map::new();\n",
                    "    g.<|>\n",
                    "    let x = 1;\n",
                    "    x\n",
                    "}\n",
                ),
                "main",
            ),
            (
                "before-control-flow",
                concat!(
                    "fn main() {\n",
                    "    let mut g = Map::new();\n",
                    "    g.<|>\n",
                    "    if true { 1 } else { 2 };\n",
                    "    loop { break 0; }\n",
                    "}\n",
                ),
                "main",
            ),
        ];

        for (name, marked_source, unexpected_label) in cases {
            let project = TestProject::new(&format!("completion-map-dot-{name}"));
            let (source, position) = source_with_cursor(marked_source);
            let (state, uri) = project.open("main.hern", &source);

            let labels = labels(completion(&state, uri, position));

            assert!(
                labels.iter().any(|label| label == "set"),
                "{name}: {labels:?}"
            );
            assert!(
                labels.iter().any(|label| label == "get"),
                "{name}: {labels:?}"
            );
            assert!(
                !labels.iter().any(|label| label == unexpected_label),
                "{name}: {labels:?}"
            );
        }
    }

    #[test]
    fn receiver_completion_hides_mut_self_methods_for_immutable_map_place() {
        let project = TestProject::new("completion-map-immutable-methods");
        let source = "let g = Map::new();\ng.\n";
        let (state, uri) = project.open("main.hern", source);

        let labels = labels(completion(&state, uri, Position::new(1, 2)));

        assert!(!labels.iter().any(|label| label == "set"));
        assert!(!labels.iter().any(|label| label == "delete"));
        assert!(labels.iter().any(|label| label == "get"));
        assert!(labels.iter().any(|label| label == "has"));
        assert!(labels.iter().any(|label| label == "size"));
    }

    #[test]
    fn receiver_completion_works_for_call_result() {
        let project = TestProject::new("completion-call-result-dot");
        let source = "read_file(\"input.txt\").\n";
        let (state, uri) = project.open("main.hern", source);

        let labels = labels(completion(&state, uri, Position::new(0, 23)));

        assert!(labels.iter().any(|label| label == "len"), "{labels:?}");
        assert!(labels.iter().any(|label| label == "lines"), "{labels:?}");
        assert!(labels.iter().any(|label| label == "trim"), "{labels:?}");
        assert!(!labels.iter().any(|label| label == "read_file"));
    }

    #[test]
    fn receiver_completion_works_for_multiline_call_result() {
        let project = TestProject::new("completion-multiline-call-result-dot");
        let (source, position) =
            source_with_cursor("let data = read_file(\"input.txt\")\n  .<|>\n");
        let (state, uri) = project.open("main.hern", &source);

        let labels = labels(completion(&state, uri, position));

        assert!(labels.iter().any(|label| label == "len"), "{labels:?}");
        assert!(labels.iter().any(|label| label == "lines"), "{labels:?}");
        assert!(labels.iter().any(|label| label == "trim"), "{labels:?}");
        assert!(!labels.iter().any(|label| label == "read_file"));
    }

    #[test]
    fn receiver_completion_works_after_chained_method_call_result() {
        let project = TestProject::new("completion-chained-method-result-dot");
        let (source, position) =
            source_with_cursor("let data = [1, 2, 3];\nlet a = data.sum().<|>\n");
        let (state, uri) = project.open("main.hern", &source);

        let labels = labels(completion(&state, uri, position));

        assert!(labels.iter().any(|label| label == "to_float"), "{labels:?}");
    }

    #[test]
    fn receiver_completion_uses_expected_lambda_param_type() {
        let project = TestProject::new("completion-map-lambda-param-type");
        let (source, position) = source_with_cursor(concat!(
            "let data = read_file(\"input.txt\")\n",
            "  .trim()\n",
            "  .lines()\n",
            "  .map(fn(line) {\n",
            "    let dir = line.<|>;\n",
            "    #{ dir }\n",
            "  });\n",
        ));
        let (state, uri) = project.open("main.hern", &source);

        let labels = labels(completion(&state, uri, position));

        assert!(labels.iter().any(|label| label == "get"), "{labels:?}");
        assert!(labels.iter().any(|label| label == "trim"), "{labels:?}");
        assert!(labels.iter().any(|label| label == "chars"), "{labels:?}");
        assert!(
            !labels.iter().any(|label| label == "read_file"),
            "{labels:?}"
        );
    }

    #[test]
    fn receiver_completion_works_after_index_expression() {
        let project = TestProject::new("completion-index-result-dot");
        let (source, position) = source_with_cursor(concat!(
            "let data = [\"Left\", \"Right\"]\n",
            "  .map(fn(line: string) {\n",
            "    let dir = line[0].<|>;\n",
            "    #{ dir }\n",
            "  });\n",
        ));
        let (state, uri) = project.open("main.hern", &source);

        let labels = labels(completion(&state, uri, position));

        assert!(labels.iter().any(|label| label == "trim"), "{labels:?}");
        assert!(labels.iter().any(|label| label == "chars"), "{labels:?}");
        assert!(
            !labels.iter().any(|label| label == "read_file"),
            "{labels:?}"
        );
    }

    #[test]
    fn receiver_completion_recovery_closes_index_brackets() {
        let project = TestProject::new("completion-index-recovery-brackets");
        let (source, position) = source_with_cursor(concat!(
            "let xs = [\"Left\", \"Right\"];\n",
            "let prefix = 0;\n",
            "let value = xs[prefix.<|>\n",
        ));
        let (state, uri) = project.open("main.hern", &source);

        let labels = labels(completion(&state, uri, position));

        assert!(labels.iter().any(|label| label == "to_float"), "{labels:?}");
        assert!(!labels.iter().any(|label| label == "xs"), "{labels:?}");
    }

    #[test]
    fn default_completion_hides_internal_names() {
        let project = TestProject::new("completion-hides-internals");
        let source = "let mut g = Map::new();\ng\n";
        let (state, uri) = project.open("main.hern", source);

        let labels = labels(completion(&state, uri, Position::new(1, 0)));

        assert!(labels.iter().any(|label| label == "g"));
        assert!(!labels.iter().any(|label| label.starts_with("__")));
    }

    #[test]
    fn imported_member_completion_hides_internal_names() {
        let ImportFixture {
            state, entry_uri, ..
        } = import_fixture(
            "completion-import-internals",
            "let dep = import \"dep\";\ndep.\n",
            "fn public() -> float { 1 }\nfn __hidden() -> float { 2 }\n#{ public: public, __hidden: __hidden }\n",
        );

        let labels = labels(completion(&state, entry_uri, Position::new(1, 4)));

        assert!(labels.iter().any(|label| label == "public"));
        assert!(!labels.iter().any(|label| label == "__hidden"));
        assert!(!labels.iter().any(|label| label.starts_with("__")));
    }
}
