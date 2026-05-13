use super::state::{CachedAnalysis, ServerState, cached_analysis};
use super::uri::uri_to_path;
use super::workspace::{
    WorkspaceAnalysis, document_source, load_document_graph_recovering, load_workspace_graphs,
};
use hern_core::ast::Program;
use hern_core::module::{GraphInference, ModuleGraph};
use lsp_types::Uri;
use std::path::PathBuf;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum SnapshotMode {
    RequireTyped,
    PreferTyped,
    RecoveringGraph,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum SnapshotQuality {
    GraphOnly,
    Typed,
}

pub(super) struct AnalysisSnapshot<'a> {
    source: String,
    path: PathBuf,
    kind: SnapshotKind<'a>,
}

enum SnapshotKind<'a> {
    BorrowedTyped(&'a CachedAnalysis),
    OwnedTyped(Box<WorkspaceAnalysis>),
    GraphOnly(Box<ModuleGraph>),
}

impl<'a> AnalysisSnapshot<'a> {
    pub(super) fn source(&self) -> &str {
        &self.source
    }

    pub(super) fn graph(&self) -> &ModuleGraph {
        match &self.kind {
            SnapshotKind::BorrowedTyped(analysis) => &analysis.graph,
            SnapshotKind::OwnedTyped(analysis) => &analysis.graph,
            SnapshotKind::GraphOnly(graph) => graph,
        }
    }

    pub(super) fn inference(&self) -> Option<&GraphInference> {
        match &self.kind {
            SnapshotKind::BorrowedTyped(analysis) => Some(&analysis.inference),
            SnapshotKind::OwnedTyped(analysis) => Some(&analysis.inference),
            SnapshotKind::GraphOnly(_) => None,
        }
    }

    pub(super) fn module(&self) -> Option<(&str, &Program)> {
        self.graph().module_for_path(&self.path)
    }

    pub(super) fn quality(&self) -> SnapshotQuality {
        match &self.kind {
            SnapshotKind::BorrowedTyped(_) | SnapshotKind::OwnedTyped(_) => SnapshotQuality::Typed,
            SnapshotKind::GraphOnly(_) => SnapshotQuality::GraphOnly,
        }
    }
}

pub(super) fn analysis_snapshot<'a>(
    state: &'a ServerState,
    uri: &Uri,
    mode: SnapshotMode,
) -> Option<AnalysisSnapshot<'a>> {
    let source = document_source(state, uri)?;
    let path = uri_to_path(uri)?;

    if mode != SnapshotMode::RecoveringGraph
        && let Some(analysis) = cached_analysis(state, uri)
    {
        return Some(AnalysisSnapshot {
            source,
            path,
            kind: SnapshotKind::BorrowedTyped(analysis),
        });
    }

    if mode != SnapshotMode::RecoveringGraph
        && let Some(analysis) = load_workspace_graphs(state, uri)
    {
        return Some(AnalysisSnapshot {
            source,
            path,
            kind: SnapshotKind::OwnedTyped(Box::new(analysis)),
        });
    }

    if mode == SnapshotMode::RequireTyped {
        return None;
    }

    let graph = load_document_graph_recovering(state, uri)?;
    Some(AnalysisSnapshot {
        source,
        path,
        kind: SnapshotKind::GraphOnly(Box::new(graph)),
    })
}
