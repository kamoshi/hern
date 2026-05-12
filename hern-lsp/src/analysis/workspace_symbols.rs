use super::state::ServerState;
use super::uri::{path_to_uri, source_span_to_range, uri_to_path};
use hern_core::pipeline::parse_source_recovering;
use hern_core::source_index::{DefinitionKind, index_program};
use lsp_types::{
    Location, OneOf, SymbolKind, Uri, WorkspaceSymbol, WorkspaceSymbolParams,
    WorkspaceSymbolResponse,
};
use std::collections::HashSet;
use std::fs;
use std::path::{Path, PathBuf};

pub(crate) fn workspace_symbols(
    state: &ServerState,
    params: WorkspaceSymbolParams,
) -> Option<WorkspaceSymbolResponse> {
    let query = params.query.trim().to_lowercase();
    let mut seen = HashSet::new();
    let mut symbols = Vec::new();

    for (uri, source) in open_workspace_documents(state) {
        collect_symbols_for_source(&uri, &source, &query, &mut symbols);
        seen.insert(uri);
    }

    for path in workspace_hern_files(state) {
        let Some(uri) = path_to_uri(&path) else {
            continue;
        };
        if !seen.insert(uri.clone()) {
            continue;
        }
        let Ok(source) = fs::read_to_string(&path) else {
            continue;
        };
        collect_symbols_for_source(&uri, &source, &query, &mut symbols);
    }

    symbols.sort_by(|a, b| {
        a.name
            .cmp(&b.name)
            .then_with(|| symbol_uri(a).cmp(&symbol_uri(b)))
    });
    Some(WorkspaceSymbolResponse::Nested(symbols))
}

fn open_workspace_documents(state: &ServerState) -> Vec<(Uri, String)> {
    state
        .documents
        .iter()
        .filter_map(|(uri, source)| {
            let path = uri_to_path(uri)?;
            is_hern_file(&path)
                .then(|| state.path_is_in_workspace(&path))
                .filter(|in_workspace| *in_workspace)?;
            Some((uri.clone(), source.clone()))
        })
        .collect()
}

fn workspace_hern_files(state: &ServerState) -> Vec<PathBuf> {
    let mut files = Vec::new();
    let roots = if state.workspace_roots.is_empty() {
        return files;
    } else {
        state.workspace_roots.clone()
    };
    for root in roots {
        collect_hern_files(&root, state.config.max_indexed_files, &mut files);
        if files.len() >= state.config.max_indexed_files {
            break;
        }
    }
    files
}

fn collect_hern_files(root: &Path, max_files: usize, files: &mut Vec<PathBuf>) {
    if files.len() >= max_files {
        return;
    }
    if root.is_file() {
        if is_hern_file(root) {
            files.push(root.to_path_buf());
        }
        return;
    }
    let Ok(entries) = fs::read_dir(root) else {
        return;
    };
    let mut entries = entries.filter_map(Result::ok).collect::<Vec<_>>();
    entries.sort_by_key(|entry| entry.path());
    for entry in entries {
        if files.len() >= max_files {
            break;
        }
        let path = entry.path();
        if path.is_dir() {
            collect_hern_files(&path, max_files, files);
        } else if is_hern_file(&path) {
            files.push(path);
        }
    }
}

fn collect_symbols_for_source(
    uri: &Uri,
    source: &str,
    query: &str,
    symbols: &mut Vec<WorkspaceSymbol>,
) {
    let Ok(parsed) = parse_source_recovering(source) else {
        return;
    };
    let index = index_program(&parsed.program);
    for definition in index.definitions {
        if !is_workspace_symbol_kind(definition.kind) || !matches_query(&definition.name, query) {
            continue;
        }
        symbols.push(WorkspaceSymbol {
            name: definition.name,
            kind: symbol_kind(definition.kind),
            tags: None,
            container_name: None,
            location: OneOf::Left(Location::new(
                uri.clone(),
                source_span_to_range(definition.location.span),
            )),
            data: None,
        });
    }
}

fn matches_query(name: &str, query: &str) -> bool {
    query.is_empty() || name.to_lowercase().contains(query)
}

fn is_workspace_symbol_kind(kind: DefinitionKind) -> bool {
    !matches!(kind, DefinitionKind::Parameter)
}

fn symbol_kind(kind: DefinitionKind) -> SymbolKind {
    match kind {
        DefinitionKind::Function => SymbolKind::FUNCTION,
        DefinitionKind::ImplMethod | DefinitionKind::TraitMethod => SymbolKind::METHOD,
        DefinitionKind::Let => SymbolKind::VARIABLE,
        DefinitionKind::Parameter => SymbolKind::VARIABLE,
        DefinitionKind::Trait => SymbolKind::INTERFACE,
        DefinitionKind::Type => SymbolKind::ENUM,
        DefinitionKind::TypeAlias => SymbolKind::STRUCT,
        DefinitionKind::Variant => SymbolKind::ENUM_MEMBER,
        DefinitionKind::Extern => SymbolKind::FUNCTION,
    }
}

fn is_hern_file(path: &Path) -> bool {
    path.extension()
        .is_some_and(|extension| extension == "hern")
}

fn symbol_uri(symbol: &WorkspaceSymbol) -> String {
    match &symbol.location {
        OneOf::Left(location) => location.uri.to_string(),
        OneOf::Right(location) => location.uri.to_string(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::analysis::tests::TestProject;

    #[test]
    fn workspace_symbols_find_definitions_across_workspace() {
        let project = TestProject::new("workspace-symbols");
        project.write("main.hern", "fn main() { helper() }\n");
        project.write(
            "dep.hern",
            "fn helper() { 1 }\ntype Maybe { Some(int), None }\n",
        );
        let mut state = ServerState::new().expect("server state should initialize");
        state.workspace_roots = vec![fs::canonicalize(&project.root).expect("root should exist")];

        let response = workspace_symbols(
            &state,
            WorkspaceSymbolParams {
                query: "hel".to_string(),
                work_done_progress_params: Default::default(),
                partial_result_params: Default::default(),
            },
        )
        .expect("workspace symbols should be available");

        let WorkspaceSymbolResponse::Nested(symbols) = response else {
            panic!("expected nested workspace symbols");
        };
        assert_eq!(symbols.len(), 1);
        assert_eq!(symbols[0].name, "helper");
        assert_eq!(symbols[0].kind, SymbolKind::FUNCTION);
    }

    #[test]
    fn workspace_symbols_include_open_unsaved_documents() {
        let project = TestProject::new("workspace-symbols-open");
        let uri = project.write("main.hern", "fn old() { 1 }\n");
        let mut state = ServerState::new().expect("server state should initialize");
        state.workspace_roots = vec![fs::canonicalize(&project.root).expect("root should exist")];
        state.set_document(uri, "fn unsaved() { 1 }\n".to_string(), 1);

        let response = workspace_symbols(
            &state,
            WorkspaceSymbolParams {
                query: "unsaved".to_string(),
                work_done_progress_params: Default::default(),
                partial_result_params: Default::default(),
            },
        )
        .expect("workspace symbols should be available");

        let WorkspaceSymbolResponse::Nested(symbols) = response else {
            panic!("expected nested workspace symbols");
        };
        assert_eq!(symbols.len(), 1);
        assert_eq!(symbols[0].name, "unsaved");
    }
}
