use super::state::{ServerState, document_overlays};
use super::uri::uri_to_path;
use hern_core::analysis::CompilerDiagnostic;
use hern_core::module::{GraphInference, ModuleGraph, infer_graph};
use hern_core::workspace::{WorkspaceInputs, analyze_workspace};
use std::fs;

pub(super) struct WorkspaceAnalysis {
    pub(super) graph: ModuleGraph,
    pub(super) inference: GraphInference,
}

pub(super) fn analyze_document_graph(
    state: &ServerState,
    uri: &lsp_types::Uri,
) -> Result<WorkspaceAnalysis, CompilerDiagnostic> {
    let mut graph = load_document_graph(state, uri)?;
    let inference = state.timed("inference", || infer_graph(&mut graph))?;
    Ok(WorkspaceAnalysis { graph, inference })
}

pub(super) fn load_document_graph(
    state: &ServerState,
    uri: &lsp_types::Uri,
) -> Result<ModuleGraph, CompilerDiagnostic> {
    let path = uri_to_path(uri).ok_or_else(|| {
        CompilerDiagnostic::error(None, format!("unsupported document URI: {}", uri.as_str()))
    })?;
    let overlays = document_overlays(state);
    state
        .timed("module graph loading", || {
            ModuleGraph::load_entry_with_prelude_and_overlays(
                &path,
                state.prelude.program.clone(),
                overlays,
            )
        })
        .map(|(graph, _)| graph)
}

/// Loads the module graph using parse-error recovery. Unlike `load_document_graph`, this
/// can return a partial graph even when the current document overlay has a syntax error —
/// making it suitable as a last-resort fallback for completion while the user is mid-edit.
/// Lex errors or missing entry-module paths can still cause this to return `None`.
pub(super) fn load_document_graph_recovering(
    state: &ServerState,
    uri: &lsp_types::Uri,
) -> Option<ModuleGraph> {
    let path = uri_to_path(uri)?;
    let overlays = document_overlays(state);
    state
        .timed("recovering module graph loading", || {
            ModuleGraph::load_entry_with_prelude_and_overlays_recovering(
                &path,
                state.prelude.program.clone(),
                overlays,
            )
        })
        .value
        .map(|loaded| loaded.graph)
}

/// Loads the graph and inference, accepting partial results even when type errors exist.
/// Unlike `analyze_document_graph`, this succeeds as long as both graph and inference
/// are available, regardless of whether there are diagnostics. Use this for hover and
/// similar features where partial inference is better than nothing.
pub(super) fn load_workspace_graphs(
    state: &ServerState,
    uri: &lsp_types::Uri,
) -> Option<WorkspaceAnalysis> {
    let path = uri_to_path(uri)?;
    let analysis = state.timed("workspace analysis", || {
        analyze_workspace(WorkspaceInputs {
            entry: path,
            overlays: document_overlays(state),
            prelude: Some(state.prelude.program.clone()),
        })
    });
    Some(WorkspaceAnalysis {
        graph: analysis.graph?,
        inference: analysis.inference?,
    })
}

pub(super) fn document_source(state: &ServerState, uri: &lsp_types::Uri) -> Option<String> {
    if let Some(source) = state.documents.get(uri) {
        return Some(source.clone());
    }
    let path = uri_to_path(uri)?;
    fs::read_to_string(path).ok()
}
