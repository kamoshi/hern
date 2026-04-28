#![allow(clippy::mutable_key_type)]
mod analysis;

use analysis::{
    DiagnosticsByUri, ServerState, combined_diagnostics_for_uri, completion, definition,
    diagnostics_for_document, hover, references, rename,
};
use lsp_server::{Connection, Message, Notification, Response};
use lsp_types::notification::{
    DidChangeTextDocument, DidCloseTextDocument, DidOpenTextDocument, Notification as _,
    PublishDiagnostics,
};
use lsp_types::request::{
    Completion, GotoDefinition, HoverRequest, References, Rename, Request as _,
};
use lsp_types::{
    CompletionOptions, CompletionParams, CompletionResponse, Diagnostic, GotoDefinitionParams,
    GotoDefinitionResponse, HoverParams, HoverProviderCapability, InitializeParams, MarkupKind,
    OneOf, PublishDiagnosticsParams, ReferenceParams, RenameParams, ServerCapabilities,
    TextDocumentSyncCapability, TextDocumentSyncKind, Uri,
};
use std::collections::HashSet;
use std::time::Duration;

const VALIDATION_DEBOUNCE: Duration = Duration::from_millis(150);

pub fn run() -> Result<(), Box<dyn std::error::Error + Sync + Send>> {
    let (connection, io_threads) = Connection::stdio();

    let capabilities = serde_json::to_value(ServerCapabilities {
        text_document_sync: Some(TextDocumentSyncCapability::Kind(TextDocumentSyncKind::FULL)),
        hover_provider: Some(HoverProviderCapability::Simple(true)),
        definition_provider: Some(OneOf::Left(true)),
        references_provider: Some(OneOf::Left(true)),
        rename_provider: Some(OneOf::Left(true)),
        completion_provider: Some(CompletionOptions {
            resolve_provider: Some(false),
            trigger_characters: None,
            ..Default::default()
        }),
        ..Default::default()
    })?;
    let init_params: InitializeParams =
        serde_json::from_value(connection.initialize(capabilities)?)?;

    let supports_markdown_hover = init_params
        .capabilities
        .text_document
        .as_ref()
        .and_then(|td| td.hover.as_ref())
        .and_then(|h| h.content_format.as_ref())
        .is_some_and(|formats| formats.contains(&MarkupKind::Markdown));

    let mut state = ServerState::new()?;
    state.supports_markdown_hover = supports_markdown_hover;
    main_loop(&connection, &mut state)?;

    io_threads.join()?;
    Ok(())
}

fn main_loop(
    conn: &Connection,
    state: &mut ServerState,
) -> Result<(), Box<dyn std::error::Error + Sync + Send>> {
    let mut pending_validations = HashSet::new();
    loop {
        match conn.receiver.recv_timeout(VALIDATION_DEBOUNCE) {
            Ok(msg) => match msg {
                Message::Request(req) => {
                    if conn.handle_shutdown(&req)? {
                        return Ok(());
                    }
                    handle_request(conn, state, req)?;
                }
                Message::Notification(notif) => {
                    handle_notification(conn, state, notif, &mut pending_validations)?;
                }
                Message::Response(_) => {}
            },
            Err(crossbeam_channel::RecvTimeoutError::Timeout) => {
                flush_pending_validations(conn, state, &mut pending_validations)?;
            }
            Err(crossbeam_channel::RecvTimeoutError::Disconnected) => return Ok(()),
        }
    }
}

fn handle_request(
    conn: &Connection,
    state: &ServerState,
    req: lsp_server::Request,
) -> Result<(), Box<dyn std::error::Error + Sync + Send>> {
    match req.method.as_str() {
        HoverRequest::METHOD => {
            let params: HoverParams = serde_json::from_value(req.params)?;
            let hover = hover(
                state,
                params.text_document_position_params.text_document.uri,
                params.text_document_position_params.position,
            );
            conn.sender
                .send(Message::Response(Response::new_ok(req.id, hover)))?;
        }
        GotoDefinition::METHOD => {
            let params: GotoDefinitionParams = serde_json::from_value(req.params)?;
            let definition = definition(
                state,
                params.text_document_position_params.text_document.uri,
                params.text_document_position_params.position,
            )
            .map(GotoDefinitionResponse::Scalar);
            conn.sender
                .send(Message::Response(Response::new_ok(req.id, definition)))?;
        }
        References::METHOD => {
            let params: ReferenceParams = serde_json::from_value(req.params)?;
            let locations = references(
                state,
                params.text_document_position.text_document.uri,
                params.text_document_position.position,
                params.context.include_declaration,
            );
            conn.sender
                .send(Message::Response(Response::new_ok(req.id, locations)))?;
        }
        Rename::METHOD => {
            let params: RenameParams = serde_json::from_value(req.params)?;
            match rename(
                state,
                params.text_document_position.text_document.uri,
                params.text_document_position.position,
                params.new_name,
            ) {
                Ok(edit) => conn
                    .sender
                    .send(Message::Response(Response::new_ok(req.id, edit)))?,
                Err(msg) => conn.sender.send(Message::Response(Response::new_err(
                    req.id,
                    lsp_server::ErrorCode::InvalidParams as i32,
                    msg,
                )))?,
            }
        }
        Completion::METHOD => {
            let params: CompletionParams = serde_json::from_value(req.params)?;
            let items = completion(
                state,
                params.text_document_position.text_document.uri,
                params.text_document_position.position,
            );
            let response = CompletionResponse::Array(items);
            conn.sender
                .send(Message::Response(Response::new_ok(req.id, Some(response))))?;
        }
        _ => {
            let resp = Response::new_err(
                req.id,
                lsp_server::ErrorCode::MethodNotFound as i32,
                format!("method not found: {}", req.method),
            );
            conn.sender.send(Message::Response(resp))?;
        }
    }
    Ok(())
}

fn handle_notification(
    conn: &Connection,
    state: &mut ServerState,
    notif: lsp_server::Notification,
    pending_validations: &mut HashSet<Uri>,
) -> Result<(), Box<dyn std::error::Error + Sync + Send>> {
    match notif.method.as_str() {
        DidOpenTextDocument::METHOD => {
            let params: lsp_types::DidOpenTextDocumentParams =
                serde_json::from_value(notif.params)?;
            let uri = params.text_document.uri;
            let affected_entries = state.entries_affected_by_document(&uri);
            state.set_document(
                uri.clone(),
                params.text_document.text,
                params.text_document.version,
            );
            // Mark before publishing so that entries_affected_by_document includes this
            // URI when the diagnostics run triggers cache-invalidation paths.
            state.mark_open_entry(uri.clone());
            publish_diagnostics(conn, state, uri.clone())?;
            schedule_dependent_validations(pending_validations, &uri, affected_entries);
        }
        DidChangeTextDocument::METHOD => {
            let params: lsp_types::DidChangeTextDocumentParams =
                serde_json::from_value(notif.params)?;
            if let Some(change) = params.content_changes.into_iter().last() {
                let uri = params.text_document.uri;
                let affected_entries = state.entries_affected_by_document(&uri);
                state.set_document(uri.clone(), change.text, params.text_document.version);
                pending_validations.extend(affected_entries);
            }
        }
        DidCloseTextDocument::METHOD => {
            let params: lsp_types::DidCloseTextDocumentParams =
                serde_json::from_value(notif.params)?;
            let uri = params.text_document.uri;
            // Capture dependent entries and entry status before mutating state.
            // Use is_open_entry (client-opened status) rather than is_known_entry
            // (has dependency tracking) — the correct criterion for "should we clear
            // entry-owned diagnostics?" is whether the client explicitly opened this
            // document, not whether it was ever analysed as an entry.
            let affected_entries = state.entries_affected_by_document(&uri);
            let was_open_entry = state.is_open_entry(&uri);
            state.unmark_open_entry(&uri);
            state.remove_document(&uri);
            pending_validations.remove(&uri);
            // Only clear entry-owned diagnostics when the closed document was explicitly
            // opened by the client as an entry. Closing a dependency-only overlay should
            // not publish empty diagnostics for it — the owning entries will re-publish
            // after revalidation below.
            if was_open_entry {
                clear_entry_diagnostics(conn, state, &uri)?;
            }
            for entry_uri in affected_entries {
                pending_validations.remove(&entry_uri);
                if entry_uri != uri {
                    publish_diagnostics(conn, state, entry_uri)?;
                }
            }
        }
        _ => {}
    }
    Ok(())
}

fn schedule_dependent_validations(
    pending_validations: &mut HashSet<Uri>,
    changed_uri: &Uri,
    affected_entries: HashSet<Uri>,
) {
    pending_validations.extend(
        affected_entries
            .into_iter()
            .filter(|entry_uri| entry_uri != changed_uri),
    );
}

fn flush_pending_validations(
    conn: &Connection,
    state: &mut ServerState,
    pending_validations: &mut HashSet<Uri>,
) -> Result<(), Box<dyn std::error::Error + Sync + Send>> {
    let uris: Vec<_> = pending_validations.drain().collect();
    for uri in uris {
        publish_diagnostics(conn, state, uri)?;
    }
    Ok(())
}

fn publish_diagnostics(
    conn: &Connection,
    state: &mut ServerState,
    uri: Uri,
) -> Result<(), Box<dyn std::error::Error + Sync + Send>> {
    let diagnostics = diagnostics_for_document(state, &uri);
    publish_entry_diagnostics(conn, state, uri, diagnostics)?;
    Ok(())
}

fn clear_entry_diagnostics(
    conn: &Connection,
    state: &mut ServerState,
    entry_uri: &Uri,
) -> Result<(), Box<dyn std::error::Error + Sync + Send>> {
    let mut affected: HashSet<Uri> = state
        .diagnostics_by_entry
        .remove(entry_uri)
        .map(|diagnostics| diagnostics.into_keys().collect())
        .unwrap_or_default();
    state.remove_entry_tracking(entry_uri);
    affected.insert(entry_uri.clone());
    for uri in affected {
        send_diagnostics(conn, uri.clone(), combined_diagnostics_for_uri(state, &uri))?;
    }
    Ok(())
}

fn publish_entry_diagnostics(
    conn: &Connection,
    state: &mut ServerState,
    entry_uri: Uri,
    diagnostics: DiagnosticsByUri,
) -> Result<(), Box<dyn std::error::Error + Sync + Send>> {
    let mut affected: HashSet<Uri> = state
        .diagnostics_by_entry
        .get(&entry_uri)
        .map(|previous| previous.keys().cloned().collect())
        .unwrap_or_default();
    affected.extend(diagnostics.keys().cloned());

    state
        .diagnostics_by_entry
        .insert(entry_uri.clone(), diagnostics);

    for uri in affected {
        send_diagnostics(conn, uri.clone(), combined_diagnostics_for_uri(state, &uri))?;
    }
    Ok(())
}

fn send_diagnostics(
    conn: &Connection,
    uri: Uri,
    diagnostics: Vec<Diagnostic>,
) -> Result<(), Box<dyn std::error::Error + Sync + Send>> {
    let params = PublishDiagnosticsParams {
        uri,
        diagnostics,
        version: None,
    };
    let notif = Notification::new(PublishDiagnostics::METHOD.to_string(), params);
    conn.sender.send(Message::Notification(notif))?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::str::FromStr;

    fn uri(value: &str) -> Uri {
        Uri::from_str(value).expect("test URI should parse")
    }

    #[test]
    fn opening_dependency_schedules_dependent_entries_but_not_opened_uri() {
        let dep = uri("file:///workspace/dep.hern");
        let entry = uri("file:///workspace/main.hern");
        let mut pending = HashSet::new();

        schedule_dependent_validations(
            &mut pending,
            &dep,
            HashSet::from([dep.clone(), entry.clone()]),
        );

        assert!(pending.contains(&entry));
        assert!(!pending.contains(&dep));
    }
}
