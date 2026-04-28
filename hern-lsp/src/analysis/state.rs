#![allow(clippy::mutable_key_type)]

use super::diagnostics::{DiagnosticsByUri, diagnostic_identity, diagnostics_from_compiler_diagnostics};
use super::uri::{path_to_uri, uri_to_path};
use hern_core::analysis::{CompilerDiagnostic, PreludeAnalysis, analyze_prelude};
use hern_core::module::{GraphInference, ModuleGraph, normalize_overlay_path};
use hern_core::workspace::{WorkspaceInputs, analyze_workspace};
use lsp_types::{Diagnostic, Uri};
use std::collections::{HashMap, HashSet};
use std::fs;
use std::path::PathBuf;
use std::time::SystemTime;

pub(crate) struct ServerState {
    pub(crate) documents: HashMap<Uri, String>,
    pub(crate) document_versions: HashMap<Uri, i32>,
    pub(crate) diagnostics_by_entry: HashMap<Uri, DiagnosticsByUri>,
    pub(super) entry_dependencies: HashMap<Uri, HashSet<Uri>>,
    pub(super) cached_analyses: HashMap<Uri, CachedAnalysis>,
    /// URIs that were explicitly opened by the client (via didOpen) and are treated as
    /// entry-point documents. A document absent from this set but present in another
    /// entry's `entry_dependencies` is dependency-only and should not get its own
    /// entry-level diagnostic lifecycle.
    pub(super) open_entry_uris: HashSet<Uri>,
    pub(super) prelude: PreludeAnalysis,
    /// Whether the client advertised `markdown` in its hover `contentFormat` capability.
    /// When false, plain text is used instead of Markdown fenced blocks.
    pub(crate) supports_markdown_hover: bool,
}

#[derive(Clone)]
pub(super) struct CachedAnalysis {
    pub(super) document_versions: HashMap<Uri, i32>,
    pub(super) file_fingerprints: HashMap<Uri, Option<FileFingerprint>>,
    pub(super) graph: ModuleGraph,
    pub(super) inference: GraphInference,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct FileFingerprint {
    pub(super) len: u64,
    pub(super) modified: Option<SystemTime>,
}

impl ServerState {
    pub(crate) fn new() -> Result<Self, CompilerDiagnostic> {
        Ok(Self {
            documents: HashMap::new(),
            document_versions: HashMap::new(),
            diagnostics_by_entry: HashMap::new(),
            entry_dependencies: HashMap::new(),
            cached_analyses: HashMap::new(),
            open_entry_uris: HashSet::new(),
            prelude: analyze_prelude()?,
            supports_markdown_hover: true,
        })
    }

    /// Marks `uri` as a client-opened entry document. Call this when a didOpen notification
    /// arrives. Does nothing if the URI is already marked.
    pub(crate) fn mark_open_entry(&mut self, uri: Uri) {
        self.open_entry_uris.insert(uri);
    }

    /// Unmarks `uri` as a client-opened entry. Call this when a didClose notification
    /// arrives before removing the document overlay.
    pub(crate) fn unmark_open_entry(&mut self, uri: &Uri) {
        self.open_entry_uris.remove(uri);
    }

    /// Returns `true` if `uri` was explicitly opened by the client and is being tracked
    /// as an entry-point document.
    pub(crate) fn is_open_entry(&self, uri: &Uri) -> bool {
        self.open_entry_uris.contains(uri)
    }

    pub(crate) fn set_document(&mut self, uri: Uri, text: String, version: i32) {
        self.documents.insert(uri.clone(), text);
        self.document_versions.insert(uri.clone(), version);
        self.invalidate_cached_analyses_for_document(&uri);
    }

    pub(crate) fn remove_document(&mut self, uri: &Uri) {
        self.documents.remove(uri);
        self.document_versions.remove(uri);
        self.invalidate_cached_analyses_for_document(uri);
    }

    pub(crate) fn invalidate_cached_analyses_for_documents(
        &mut self,
        uris: impl IntoIterator<Item = Uri>,
    ) -> HashSet<Uri> {
        let mut affected = HashSet::new();
        for uri in uris {
            affected.extend(self.invalidate_cached_analyses_for_document(&uri));
        }
        affected
    }

    pub(crate) fn entries_affected_by_document(&self, uri: &Uri) -> HashSet<Uri> {
        // Only treat `uri` itself as an affected entry if the client opened it as one.
        // A document that appears only as a dependency of another entry should not be
        // re-analysed independently when it changes — the owning entries handle that.
        let mut entries = if self.open_entry_uris.contains(uri) {
            HashSet::from([uri.clone()])
        } else {
            HashSet::new()
        };
        entries.extend(
            self.entry_dependencies
                .iter()
                .filter(|(_, dependencies)| dependencies.contains(uri))
                .map(|(entry, _)| entry.clone()),
        );
        entries
    }

    fn invalidate_cached_analyses_for_document(&mut self, uri: &Uri) -> HashSet<Uri> {
        let affected = self.entries_affected_by_document(uri);
        for entry in &affected {
            self.cached_analyses.remove(&entry);
        }
        affected
    }

    fn update_entry_dependencies(
        &mut self,
        entry_uri: &Uri,
        graph: Option<&ModuleGraph>,
    ) -> HashSet<Uri> {
        let dependencies = graph
            .map(graph_module_uris)
            .unwrap_or_else(|| HashSet::from([entry_uri.clone()]));
        self.entry_dependencies
            .insert(entry_uri.clone(), dependencies.clone());
        dependencies
    }

    pub(crate) fn remove_entry_tracking(&mut self, entry_uri: &Uri) {
        self.entry_dependencies.remove(entry_uri);
        self.cached_analyses.remove(entry_uri);
    }
}

pub(crate) fn diagnostics_for_document(
    state: &mut ServerState,
    entry_uri: &Uri,
) -> DiagnosticsByUri {
    use hern_core::pipeline::parse_source_recovering;

    if let Some(source) = state.documents.get(entry_uri) {
        match parse_source_recovering(source) {
            Ok(parsed) if !parsed.diagnostics.is_empty() => {
                state.update_entry_dependencies(entry_uri, None);
                return diagnostics_from_compiler_diagnostics(entry_uri, parsed.diagnostics);
            }
            Ok(_) => {}
            Err(diagnostic) => {
                state.update_entry_dependencies(entry_uri, None);
                return diagnostics_from_compiler_diagnostics(entry_uri, vec![diagnostic]);
            }
        }
    }

    let path = match uri_to_path(entry_uri) {
        Some(path) => path,
        None => {
            return diagnostics_from_compiler_diagnostics(
                entry_uri,
                vec![CompilerDiagnostic::error(
                    None,
                    format!("unsupported document URI: {}", entry_uri.as_str()),
                )],
            );
        }
    };
    let analysis = analyze_workspace(WorkspaceInputs {
        entry: path,
        overlays: document_overlays(state),
        prelude: Some(state.prelude.program.clone()),
    });
    let dependencies = state.update_entry_dependencies(entry_uri, analysis.graph.as_ref());
    if analysis.diagnostics.is_empty()
        && let (Some(graph), Some(inference)) = (analysis.graph, analysis.inference)
    {
        state.cached_analyses.insert(
            entry_uri.clone(),
            CachedAnalysis {
                document_versions: document_versions_for_uris(state, &dependencies),
                file_fingerprints: file_fingerprints_for_uris(state, &dependencies),
                graph,
                inference,
            },
        );
    }
    diagnostics_from_compiler_diagnostics(entry_uri, analysis.diagnostics)
}

pub(crate) fn combined_diagnostics_for_uri(state: &ServerState, uri: &Uri) -> Vec<Diagnostic> {
    let mut diagnostics = Vec::new();
    let mut seen = std::collections::HashSet::new();
    for by_uri in state.diagnostics_by_entry.values() {
        if let Some(items) = by_uri.get(uri) {
            for diagnostic in items {
                if seen.insert(diagnostic_identity(diagnostic)) {
                    diagnostics.push(diagnostic.clone());
                }
            }
        }
    }
    diagnostics
}

pub(super) fn cached_analysis<'a>(state: &'a ServerState, entry_uri: &Uri) -> Option<&'a CachedAnalysis> {
    let analysis = state.cached_analyses.get(entry_uri)?;
    let open_documents_match = analysis
        .document_versions
        .iter()
        .all(|(uri, version)| state.document_versions.get(uri) == Some(version));
    let closed_files_match = analysis
        .file_fingerprints
        .iter()
        .all(|(uri, fingerprint)| file_fingerprint_for_uri(uri) == *fingerprint);
    (open_documents_match && closed_files_match).then_some(analysis)
}

pub(super) fn document_overlays(state: &ServerState) -> HashMap<PathBuf, String> {
    state
        .documents
        .iter()
        .filter_map(|(uri, source)| {
            let path = uri_to_path(uri)?;
            Some((normalize_overlay_path(&path), source.clone()))
        })
        .collect()
}

fn graph_module_uris(graph: &ModuleGraph) -> HashSet<Uri> {
    graph
        .paths
        .values()
        .filter_map(|p| path_to_uri(p))
        .collect()
}

fn document_versions_for_uris(state: &ServerState, uris: &HashSet<Uri>) -> HashMap<Uri, i32> {
    uris.iter()
        .filter_map(|uri| {
            let version = state.document_versions.get(uri)?;
            Some((uri.clone(), *version))
        })
        .collect()
}

fn file_fingerprints_for_uris(
    state: &ServerState,
    uris: &HashSet<Uri>,
) -> HashMap<Uri, Option<FileFingerprint>> {
    uris.iter()
        .filter(|uri| !state.documents.contains_key(*uri))
        .map(|uri| (uri.clone(), file_fingerprint_for_uri(uri)))
        .collect()
}

fn file_fingerprint_for_uri(uri: &Uri) -> Option<FileFingerprint> {
    let path = uri_to_path(uri)?;
    let metadata = fs::metadata(path).ok()?;
    Some(FileFingerprint {
        len: metadata.len(),
        modified: metadata.modified().ok(),
    })
}
