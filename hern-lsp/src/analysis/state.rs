#![allow(clippy::mutable_key_type)]

use super::diagnostics::{
    DiagnosticsByUri, diagnostic_identity, diagnostics_from_compiler_diagnostics,
};
use super::uri::{path_to_uri, uri_to_path};
use hern_core::analysis::{CompilerDiagnostic, PreludeAnalysis, analyze_prelude};
use hern_core::module::{GraphInference, ModuleGraph, normalize_overlay_path};
use hern_core::workspace::{WorkspaceInputs, analyze_workspace};
use lsp_types::{Diagnostic, InitializeParams, Uri};
use std::cell::Cell;
use std::collections::{HashMap, HashSet};
use std::fs;
use std::path::{Path, PathBuf};
use std::time::{Duration, Instant, SystemTime};

const DEFAULT_DIAGNOSTICS_DEBOUNCE: Duration = Duration::from_millis(150);

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
    pub(crate) workspace_roots: Vec<PathBuf>,
    pub(crate) config: LspConfig,
    pub(crate) perf: LspPerf,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct LspConfig {
    pub(crate) diagnostics_debounce: Duration,
    pub(crate) max_indexed_files: usize,
    pub(crate) debug_timing: bool,
}

impl Default for LspConfig {
    fn default() -> Self {
        Self {
            diagnostics_debounce: DEFAULT_DIAGNOSTICS_DEBOUNCE,
            max_indexed_files: 10_000,
            debug_timing: false,
        }
    }
}

#[derive(Default)]
pub(crate) struct LspPerf {
    pub(crate) cache_hits: Cell<u64>,
    pub(crate) cache_misses: Cell<u64>,
    pub(crate) document_invalidations: Cell<u64>,
    pub(crate) watched_file_invalidations: Cell<u64>,
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
            workspace_roots: Vec::new(),
            config: LspConfig::default(),
            perf: LspPerf::default(),
        })
    }

    pub(crate) fn configure_from_initialize(&mut self, params: &InitializeParams) {
        self.workspace_roots = workspace_roots_from_initialize(params);
        self.config = lsp_config_from_initialize(params);
    }

    pub(crate) fn path_is_in_workspace(&self, path: &Path) -> bool {
        if self.workspace_roots.is_empty() {
            return true;
        }
        let normalized = normalize_overlay_path(path);
        self.workspace_roots
            .iter()
            .any(|root| normalized.starts_with(root))
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
        let affected = self.invalidate_cached_analyses_for_document(&uri);
        self.perf
            .document_invalidations
            .set(self.perf.document_invalidations.get() + affected.len() as u64);
    }

    pub(crate) fn remove_document(&mut self, uri: &Uri) {
        self.documents.remove(uri);
        self.document_versions.remove(uri);
        let affected = self.invalidate_cached_analyses_for_document(uri);
        self.perf
            .document_invalidations
            .set(self.perf.document_invalidations.get() + affected.len() as u64);
    }

    pub(crate) fn invalidate_cached_analyses_for_documents(
        &mut self,
        uris: impl IntoIterator<Item = Uri>,
    ) -> HashSet<Uri> {
        let mut affected = HashSet::new();
        for uri in uris {
            affected.extend(self.invalidate_cached_analyses_for_document(&uri));
        }
        self.perf
            .watched_file_invalidations
            .set(self.perf.watched_file_invalidations.get() + affected.len() as u64);
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

    pub(super) fn timed<T>(&self, label: &str, f: impl FnOnce() -> T) -> T {
        if !self.config.debug_timing {
            return f();
        }
        let start = Instant::now();
        let result = f();
        eprintln!("hern-lsp timing {label}: {:?}", start.elapsed());
        result
    }
}

fn workspace_roots_from_initialize(params: &InitializeParams) -> Vec<PathBuf> {
    let mut roots = Vec::new();
    if let Some(folders) = &params.workspace_folders {
        for folder in folders {
            if let Some(path) = uri_to_path(&folder.uri) {
                roots.push(normalize_overlay_path(&path));
            }
        }
    }
    if roots.is_empty() {
        #[allow(deprecated)]
        if let Some(root_uri) = &params.root_uri
            && let Some(path) = uri_to_path(root_uri)
        {
            roots.push(normalize_overlay_path(&path));
        }
    }
    roots.sort();
    roots.dedup();
    roots
}

fn lsp_config_from_initialize(params: &InitializeParams) -> LspConfig {
    let mut config = LspConfig::default();
    let Some(options) = params.initialization_options.as_ref() else {
        return config;
    };
    if let Some(ms) = options
        .get("diagnosticsDebounceMs")
        .and_then(serde_json::Value::as_u64)
    {
        config.diagnostics_debounce = Duration::from_millis(ms);
    }
    if let Some(max) = options
        .get("maxIndexedFiles")
        .and_then(serde_json::Value::as_u64)
    {
        config.max_indexed_files = max as usize;
    }
    if let Some(debug) = options
        .get("debugTiming")
        .and_then(serde_json::Value::as_bool)
    {
        config.debug_timing = debug;
    }
    config
}

#[cfg(test)]
mod tests {
    use super::*;
    use lsp_types::WorkspaceFolder;

    #[test]
    fn initialize_configuration_sets_workspace_roots_and_options() {
        let root = std::env::temp_dir().join("hern-lsp-workspace-root");
        let root_uri = path_to_uri(&root).expect("root URI should encode");
        let params = InitializeParams {
            workspace_folders: Some(vec![WorkspaceFolder {
                uri: root_uri,
                name: "root".to_string(),
            }]),
            initialization_options: Some(serde_json::json!({
                "diagnosticsDebounceMs": 25,
                "maxIndexedFiles": 123,
                "debugTiming": true
            })),
            ..InitializeParams::default()
        };

        let mut state = ServerState::new().expect("server state should initialize");
        state.configure_from_initialize(&params);

        assert_eq!(state.workspace_roots, vec![normalize_overlay_path(&root)]);
        assert_eq!(state.config.diagnostics_debounce, Duration::from_millis(25));
        assert_eq!(state.config.max_indexed_files, 123);
        assert!(state.config.debug_timing);
    }

    #[test]
    fn path_workspace_check_respects_configured_roots() {
        let mut state = ServerState::new().expect("server state should initialize");
        state.workspace_roots = vec![PathBuf::from("/workspace/project")];

        assert!(state.path_is_in_workspace(Path::new("/workspace/project/src/main.hern")));
        assert!(!state.path_is_in_workspace(Path::new("/workspace/other/main.hern")));
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
    let analysis = state.timed("workspace analysis", || {
        analyze_workspace(WorkspaceInputs {
            entry: path,
            overlays: document_overlays(state),
            prelude: Some(state.prelude.program.clone()),
        })
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

pub(super) fn cached_analysis<'a>(
    state: &'a ServerState,
    entry_uri: &Uri,
) -> Option<&'a CachedAnalysis> {
    let Some(analysis) = state.cached_analyses.get(entry_uri) else {
        state
            .perf
            .cache_misses
            .set(state.perf.cache_misses.get() + 1);
        return None;
    };
    let open_documents_match = analysis
        .document_versions
        .iter()
        .all(|(uri, version)| state.document_versions.get(uri) == Some(version));
    let closed_files_match = analysis
        .file_fingerprints
        .iter()
        .all(|(uri, fingerprint)| file_fingerprint_for_uri(uri) == *fingerprint);
    if open_documents_match && closed_files_match {
        state.perf.cache_hits.set(state.perf.cache_hits.get() + 1);
        Some(analysis)
    } else {
        state
            .perf
            .cache_misses
            .set(state.perf.cache_misses.get() + 1);
        None
    }
}

pub(super) fn document_overlays(state: &ServerState) -> HashMap<PathBuf, String> {
    state.timed("overlay construction", || {
        state
            .documents
            .iter()
            .filter_map(|(uri, source)| {
                let path = uri_to_path(uri)?;
                Some((normalize_overlay_path(&path), source.clone()))
            })
            .collect()
    })
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
