mod code_actions;
mod completion;
mod diagnostics;
mod document_symbols;
mod hover;
mod navigation;
mod rename;
mod semantic_tokens;
mod signature_help;
mod state;
mod uri;
mod workspace;

pub(crate) use code_actions::code_actions;
pub(crate) use completion::completion;
pub(crate) use diagnostics::DiagnosticsByUri;
pub(crate) use document_symbols::document_symbols;
pub(crate) use hover::hover;
pub(crate) use navigation::{definition, document_highlights, references};
pub(crate) use rename::{prepare_rename, rename};
pub(crate) use semantic_tokens::legend as semantic_tokens_legend;
pub(crate) use signature_help::signature_help;
pub(crate) use state::{ServerState, combined_diagnostics_for_uri, diagnostics_for_document};

use uri::uri_to_path;

pub(crate) fn semantic_tokens(
    state: &ServerState,
    uri: lsp_types::Uri,
) -> Option<lsp_types::SemanticTokensResult> {
    let source = workspace::document_source(state, &uri)?;
    let path = uri_to_path(&uri)?;
    if let Some(analysis) = state::cached_analysis(state, &uri)
        && let Some((module_name, program)) = analysis.graph.module_for_path(&path)
    {
        return Some(state.timed("semantic tokens", || {
            semantic_tokens::semantic_tokens_for_source(
                &source,
                Some(program),
                semantic_tokens::SemanticContext::new(&analysis.inference, module_name),
            )
        }));
    }
    if let Some(analysis) = workspace::load_workspace_graphs(state, &uri)
        && let Some((module_name, program)) = analysis.graph.module_for_path(&path)
    {
        return Some(state.timed("semantic tokens", || {
            semantic_tokens::semantic_tokens_for_source(
                &source,
                Some(program),
                semantic_tokens::SemanticContext::new(&analysis.inference, module_name),
            )
        }));
    }
    let graph = workspace::load_document_graph_recovering(state, &uri)?;
    let program = graph.module_for_path(&path).map(|(_, program)| program);
    Some(state.timed("semantic tokens", || {
        semantic_tokens::semantic_tokens_for_source(&source, program, None)
    }))
}

#[cfg(test)]
pub(super) mod tests {
    use super::uri::path_to_uri;
    use super::*;
    use hern_core::analysis::analyze_prelude;
    use lsp_types::{
        CompletionItem, Diagnostic, DiagnosticSeverity, Hover, HoverContents, MarkupContent,
        Position, Range, Uri,
    };
    use std::collections::{HashMap, HashSet};
    use std::fs;
    use std::path::PathBuf;
    use std::str::FromStr;
    use std::time::{SystemTime, UNIX_EPOCH};

    pub(super) fn uri(value: &str) -> Uri {
        Uri::from_str(value).expect("test URI should parse")
    }

    pub(super) fn diagnostic(message: &str) -> Diagnostic {
        Diagnostic {
            range: Range::new(Position::new(0, 0), Position::new(0, 1)),
            severity: Some(DiagnosticSeverity::ERROR),
            message: message.to_string(),
            ..Default::default()
        }
    }

    pub(super) fn temp_dir(name: &str) -> PathBuf {
        let path = std::env::temp_dir().join(format!(
            "hern-lsp-{name}-{}-{}",
            std::process::id(),
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .expect("system time should be after epoch")
                .as_nanos()
        ));
        fs::create_dir_all(&path).expect("temp test directory should be created");
        path
    }

    pub(super) fn state_with_document(uri: Uri, source: String) -> ServerState {
        let mut state = ServerState::new().expect("server state should initialize");
        state.set_document(uri.clone(), source, 0);
        state.mark_open_entry(uri);
        state
    }

    pub(super) struct TestProject {
        pub(super) root: PathBuf,
    }

    impl TestProject {
        pub(super) fn new(name: &str) -> Self {
            Self {
                root: temp_dir(name),
            }
        }

        pub(super) fn write(&self, relative_path: &str, source: &str) -> Uri {
            let path = self.root.join(relative_path);
            if let Some(parent) = path.parent() {
                fs::create_dir_all(parent).expect("test parent directory should be created");
            }
            fs::write(&path, source).expect("test source should be written");
            path_to_uri(&fs::canonicalize(&path).expect("test path should canonicalize"))
                .expect("test URI should encode")
        }

        pub(super) fn open(&self, relative_path: &str, source: &str) -> (ServerState, Uri) {
            let uri = self.write(relative_path, source);
            (state_with_document(uri.clone(), source.to_string()), uri)
        }
    }

    pub(super) struct ImportFixture {
        pub(super) state: ServerState,
        pub(super) entry_uri: Uri,
        pub(super) dep_uri: Uri,
    }

    pub(super) fn import_fixture(
        name: &str,
        entry_source: &str,
        dep_source: &str,
    ) -> ImportFixture {
        let project = TestProject::new(name);
        let entry_uri = project.write("main.hern", entry_source);
        let dep_uri = project.write("dep.hern", dep_source);
        let state = state_with_document(entry_uri.clone(), entry_source.to_string());

        ImportFixture {
            state,
            entry_uri,
            dep_uri,
        }
    }

    pub(super) fn hover_text(hover: Hover) -> String {
        match hover.contents {
            HoverContents::Markup(MarkupContent { value, .. }) => {
                // Strip the ```hern ... ``` fences added by type_hover.
                value
                    .trim()
                    .strip_prefix("```hern\n")
                    .and_then(|s| s.strip_suffix("\n```"))
                    .unwrap_or(&value)
                    .to_string()
            }
            other => panic!("unexpected hover contents: {other:?}"),
        }
    }

    pub(super) fn completion_insert_name(item: &CompletionItem) -> &str {
        item.insert_text.as_deref().unwrap_or(&item.label)
    }

    #[test]
    fn diagnostics_from_compiler_diagnostics_routes_source_path_to_that_uri() {
        use diagnostics::diagnostics_from_compiler_diagnostics;
        use hern_core::analysis::{CompilerDiagnostic, DiagnosticSource};
        use hern_core::ast::SourceSpan;

        let entry = uri("file:///workspace/main.hern");
        let dep_path = PathBuf::from("/workspace/dep.hern");
        let diagnostic = CompilerDiagnostic::error_in(
            DiagnosticSource::Path(dep_path),
            Some(SourceSpan {
                start_line: 1,
                start_col: 1,
                end_line: 1,
                end_col: 2,
            }),
            "dep failed",
        );

        let diagnostics = diagnostics_from_compiler_diagnostics(&entry, vec![diagnostic]);
        let dep = uri("file:///workspace/dep.hern");

        assert!(diagnostics.get(&entry).is_some_and(Vec::is_empty));
        assert_eq!(diagnostics[&dep].len(), 1);
        assert_eq!(diagnostics[&dep][0].message, "dep failed");
    }

    #[test]
    fn combined_diagnostics_keep_other_entry_contributions() {
        let dep = uri("file:///workspace/dep.hern");
        let entry_a = uri("file:///workspace/a.hern");
        let entry_b = uri("file:///workspace/b.hern");

        let mut state = ServerState {
            documents: HashMap::new(),
            document_versions: HashMap::new(),
            diagnostics_by_entry: HashMap::new(),
            entry_dependencies: HashMap::new(),
            cached_analyses: HashMap::new(),
            open_entry_uris: HashSet::new(),
            prelude: analyze_prelude().expect("prelude should analyze"),
            supports_markdown_hover: true,
            workspace_roots: Vec::new(),
            config: state::LspConfig::default(),
            perf: state::LspPerf::default(),
        };
        state.diagnostics_by_entry.insert(
            entry_a.clone(),
            HashMap::from([(dep.clone(), vec![diagnostic("a")])]),
        );
        state.diagnostics_by_entry.insert(
            entry_b.clone(),
            HashMap::from([(dep.clone(), vec![diagnostic("b")])]),
        );

        state.diagnostics_by_entry.remove(&entry_a);
        let combined = combined_diagnostics_for_uri(&state, &dep);

        assert_eq!(combined.len(), 1);
        assert_eq!(combined[0].message, "b");
    }

    #[test]
    fn diagnostics_for_document_reports_multiple_parse_errors() {
        let entry = uri("file:///workspace/main.hern");
        let mut state = ServerState {
            documents: HashMap::from([(entry.clone(), "let a = ;\nlet b = ;\n".to_string())]),
            document_versions: HashMap::from([(entry.clone(), 0)]),
            diagnostics_by_entry: HashMap::new(),
            entry_dependencies: HashMap::new(),
            cached_analyses: HashMap::new(),
            open_entry_uris: HashSet::new(),
            prelude: analyze_prelude().expect("prelude should analyze"),
            supports_markdown_hover: true,
            workspace_roots: Vec::new(),
            config: state::LspConfig::default(),
            perf: state::LspPerf::default(),
        };

        let diagnostics = diagnostics_for_document(&mut state, &entry);
        let entry_diagnostics = diagnostics
            .get(&entry)
            .expect("parse diagnostics should target entry URI");

        assert_eq!(entry_diagnostics.len(), 2);
        assert_eq!(entry_diagnostics[0].range.start.line, 0);
        assert_eq!(entry_diagnostics[1].range.start.line, 1);

        state.documents.clear();
    }

    #[test]
    fn diagnostics_for_document_reports_imported_parse_errors() {
        let ImportFixture {
            mut state,
            entry_uri,
            dep_uri,
        } = import_fixture(
            "import-recovery",
            "let dep = import \"dep\";\n",
            "let a = ;\nlet b = ;\n",
        );

        let diagnostics = diagnostics_for_document(&mut state, &entry_uri);
        let dep_diagnostics = diagnostics
            .get(&dep_uri)
            .expect("imported diagnostics should target dep URI");

        assert_eq!(dep_diagnostics.len(), 2);
        assert_eq!(dep_diagnostics[0].range.start.line, 0);
        assert_eq!(dep_diagnostics[1].range.start.line, 1);
    }

    #[test]
    fn diagnostics_for_document_reports_missing_semicolon_in_function_body() {
        // The recovering parser treats the unsemiconed expression as a stmt and continues,
        // but must still emit a diagnostic so the user sees the error.
        let entry = uri("file:///workspace/main.hern");
        let source = "fn sum(steps) {\n  let mut total = 0;\n  total\n  total\n}\n";
        let mut state = ServerState {
            documents: HashMap::from([(entry.clone(), source.to_string())]),
            document_versions: HashMap::from([(entry.clone(), 0)]),
            diagnostics_by_entry: HashMap::new(),
            entry_dependencies: HashMap::new(),
            cached_analyses: HashMap::new(),
            open_entry_uris: HashSet::new(),
            prelude: analyze_prelude().expect("prelude should analyze"),
            supports_markdown_hover: true,
            workspace_roots: Vec::new(),
            config: state::LspConfig::default(),
            perf: state::LspPerf::default(),
        };

        let diagnostics = diagnostics_for_document(&mut state, &entry);
        let entry_diagnostics = diagnostics
            .get(&entry)
            .expect("diagnostics should target entry URI");

        assert!(
            !entry_diagnostics.is_empty(),
            "missing semicolon should produce a diagnostic; got none"
        );
        let messages: Vec<_> = entry_diagnostics
            .iter()
            .map(|d| d.message.as_str())
            .collect();
        assert!(
            messages.iter().any(|m| m.contains("`;`")),
            "expected a missing-semicolon diagnostic; got {:?}",
            messages
        );

        state.documents.clear();
    }

    #[test]
    fn diagnostics_record_entry_dependencies() {
        let ImportFixture {
            mut state,
            entry_uri,
            dep_uri,
        } = import_fixture(
            "entry-dependencies",
            "let dep = import \"dep\";\ndep.value\n",
            "#{ value: 1 }\n",
        );

        let diagnostics = diagnostics_for_document(&mut state, &entry_uri);

        assert!(diagnostics[&entry_uri].is_empty());
        assert!(
            state
                .entry_dependencies
                .get(&entry_uri)
                .is_some_and(|dependencies| dependencies.contains(&dep_uri))
        );
        assert!(
            state
                .entries_affected_by_document(&dep_uri)
                .contains(&entry_uri)
        );
    }

    #[test]
    fn imported_document_change_invalidates_dependent_entry_cache() {
        let ImportFixture {
            mut state,
            entry_uri,
            dep_uri,
        } = import_fixture(
            "dependency-cache-invalidation",
            "let dep = import \"dep\";\ndep.value\n",
            "#{ value: 1 }\n",
        );

        diagnostics_for_document(&mut state, &entry_uri);
        assert!(state.cached_analyses.contains_key(&entry_uri));

        state.set_document(dep_uri, "#{ value: 2 }\n".to_string(), 1);

        assert!(!state.cached_analyses.contains_key(&entry_uri));
    }

    #[test]
    fn closed_imported_file_edit_makes_cached_analysis_stale() {
        let ImportFixture {
            mut state,
            entry_uri,
            dep_uri,
        } = import_fixture(
            "closed-dependency-fingerprint",
            "let dep = import \"dep\";\ndep.value\n",
            "#{ value: 1 }\n",
        );

        diagnostics_for_document(&mut state, &entry_uri);
        assert!(state::cached_analysis(&state, &entry_uri).is_some());

        let dep_path = uri_to_path(&dep_uri).expect("dep URI should resolve to path");
        fs::write(&dep_path, "#{ value: 12345 }\n").expect("dep file should be updated");

        assert!(
            state::cached_analysis(&state, &entry_uri).is_none(),
            "closed dependency fingerprint change should make cache unusable"
        );
    }

    #[test]
    fn closed_imported_file_delete_makes_cached_analysis_stale_and_reports_import_error() {
        let ImportFixture {
            mut state,
            entry_uri,
            dep_uri,
        } = import_fixture(
            "closed-dependency-delete",
            "let dep = import \"dep\";\ndep.value\n",
            "#{ value: 1 }\n",
        );

        diagnostics_for_document(&mut state, &entry_uri);
        assert!(state::cached_analysis(&state, &entry_uri).is_some());

        let dep_path = uri_to_path(&dep_uri).expect("dep URI should resolve to path");
        fs::remove_file(&dep_path).expect("dep file should be deleted");

        assert!(state::cached_analysis(&state, &entry_uri).is_none());
        let diagnostics = diagnostics_for_document(&mut state, &entry_uri);
        let messages: Vec<_> = diagnostics
            .values()
            .flat_map(|items| items.iter())
            .map(|diagnostic| diagnostic.message.as_str())
            .collect();
        assert!(
            messages
                .iter()
                .any(|message| message.contains("error resolving file")),
            "deleted dependency should report import resolution error; got {:?}",
            messages
        );
    }

    #[test]
    fn watched_file_change_invalidates_dependent_entry_cache() {
        let ImportFixture {
            mut state,
            entry_uri,
            dep_uri,
        } = import_fixture(
            "watched-file-invalidation",
            "let dep = import \"dep\";\ndep.value\n",
            "#{ value: 1 }\n",
        );

        diagnostics_for_document(&mut state, &entry_uri);
        assert!(state.cached_analyses.contains_key(&entry_uri));

        let affected = state.invalidate_cached_analyses_for_documents([dep_uri]);

        assert!(affected.contains(&entry_uri));
        assert!(!state.cached_analyses.contains_key(&entry_uri));
    }

    #[test]
    fn unrelated_document_change_keeps_entry_cache_usable() {
        let project = TestProject::new("unrelated-cache-invalidation");
        let entry_a_source = "let dep = import \"dep_a\";\ndep.value\n";
        let entry_b_source = "let dep = import \"dep_b\";\ndep.value\n";
        let entry_a_uri = project.write("main_a.hern", entry_a_source);
        let entry_b_uri = project.write("main_b.hern", entry_b_source);
        let dep_a_uri = project.write("dep_a.hern", "#{ value: 1 }\n");
        project.write("dep_b.hern", "#{ value: 2 }\n");
        let mut state = ServerState::new().expect("server state should initialize");
        state.set_document(entry_a_uri.clone(), entry_a_source.to_string(), 0);
        state.set_document(entry_b_uri.clone(), entry_b_source.to_string(), 0);

        diagnostics_for_document(&mut state, &entry_a_uri);
        diagnostics_for_document(&mut state, &entry_b_uri);
        assert!(state::cached_analysis(&state, &entry_a_uri).is_some());
        assert!(state::cached_analysis(&state, &entry_b_uri).is_some());

        state.set_document(dep_a_uri, "#{ value: 3 }\n".to_string(), 1);

        assert!(state::cached_analysis(&state, &entry_a_uri).is_none());
        assert!(state::cached_analysis(&state, &entry_b_uri).is_some());
    }

    #[test]
    fn imported_open_document_changes_entry_diagnostics_without_disk_write() {
        let ImportFixture {
            mut state,
            entry_uri,
            dep_uri,
        } = import_fixture(
            "dependency-overlay-diagnostics",
            "let dep = import \"dep\";\ndep.value\n",
            "#{ value: 1 }\n",
        );

        assert!(diagnostics_for_document(&mut state, &entry_uri)[&entry_uri].is_empty());

        state.set_document(dep_uri.clone(), "let broken = ;\n".to_string(), 1);
        let diagnostics = diagnostics_for_document(&mut state, &entry_uri);
        let dep_diagnostics = diagnostics
            .get(&dep_uri)
            .expect("dependency diagnostics should target the dependency URI");

        assert_eq!(dep_diagnostics.len(), 1);
    }

    #[test]
    fn hover_returns_inferred_type_for_local_expression() {
        let project = TestProject::new("local-hover");
        let source = "let value = 1;\nvalue\n";
        let (state, uri) = project.open("main.hern", source);

        let info = hover(&state, uri, Position::new(1, 1)).expect("hover should resolve");

        assert_eq!(hover_text(info), "f64");
    }

    #[test]
    fn hover_normalizes_free_type_vars_for_expressions() {
        let project = TestProject::new("normalized-expression-hover");
        let source = "[]\n";
        let (state, uri) = project.open("main.hern", source);

        let info = hover(&state, uri, Position::new(0, 1)).expect("hover should resolve");

        assert_eq!(hover_text(info), "['a]");
    }

    #[test]
    fn display_names_type_vars_by_visible_type_order() {
        use hern_core::types::Ty;
        let ty = Ty::Func(
            vec![Ty::Var(78), Ty::Tuple(vec![Ty::Var(12), Ty::Var(78)])],
            Box::new(Ty::Var(12)),
        );

        assert_eq!(hover::ty_to_display_string(&ty), "fn('a, ('b, 'a)) -> 'b");
    }

    #[test]
    fn hover_reuses_type_var_names_within_polymorphic_function() {
        let project = TestProject::new("polymorphic-function-hover");
        let source = "fn choose(x, y) { x }\nchoose\n";
        let (state, uri) = project.open("main.hern", source);

        let info = hover(&state, uri, Position::new(1, 1)).expect("hover should resolve");

        assert_eq!(hover_text(info), "fn('a, 'b) -> 'a");
    }

    #[test]
    fn hover_uses_partial_inference_when_module_has_type_errors() {
        let project = TestProject::new("partial-hover");
        let source = "let value = 1;\nlet bad: bool = 2;\nvalue\n";
        let (state, uri) = project.open("main.hern", source);

        let info = hover(&state, uri, Position::new(2, 1)).expect("hover should resolve");

        assert_eq!(hover_text(info), "f64");
    }

    #[test]
    fn hover_returns_impl_method_signature() {
        let project = TestProject::new("impl-method-hover");
        let source = concat!(
            "trait Bump 'a {\n",
            "  fn bump(x: 'a) -> 'a\n",
            "}\n",
            "impl Bump for f64 {\n",
            "  fn bump(x: f64) -> f64 { x + 1 }\n",
            "}\n",
        );
        let (state, uri) = project.open("main.hern", source);

        let info = hover(&state, uri, Position::new(4, 5)).expect("hover should resolve");

        assert_eq!(hover_text(info), "fn(f64) -> f64");
    }

    #[test]
    fn hover_returns_type_and_trait_declarations() {
        let project = TestProject::new("type-trait-hover");
        let source = concat!(
            "type Pair = #{ x: f64, y: f64 }\n",
            "type Option2('a) = Some2('a) | None2\n",
            "trait Show 'a {\n",
            "  fn show(x: 'a) -> string\n",
            "}\n",
        );
        let (state, uri) = project.open("main.hern", source);

        let alias = hover(&state, uri.clone(), Position::new(0, 6)).expect("alias hover");
        let sum = hover(&state, uri.clone(), Position::new(1, 6)).expect("type hover");
        let trait_info = hover(&state, uri.clone(), Position::new(2, 7)).expect("trait hover");
        let trait_method = hover(&state, uri, Position::new(3, 5)).expect("trait method hover");

        assert_eq!(hover_text(alias), "type Pair = #{ x: f64, y: f64 }");
        assert_eq!(hover_text(sum), "type Option2('a) = Some2('a) | None2");
        assert_eq!(hover_text(trait_info), "trait Show 'a");
        assert_eq!(hover_text(trait_method), "fn show(x: 'a) -> string");
    }

    #[test]
    fn hover_uses_imported_module_types() {
        let source = "let dep = import \"dep\";\ndep.value()\n";
        let ImportFixture {
            state, entry_uri, ..
        } = import_fixture(
            "import-hover",
            source,
            "fn value() { 1 }\n#{ value: value }\n",
        );

        let info = hover(&state, entry_uri, Position::new(1, 10)).expect("hover should resolve");

        assert_eq!(hover_text(info), "f64");
    }

    #[test]
    fn hover_prefers_callee_symbol_type_inside_call() {
        let project = TestProject::new("callee-hover");
        let source = "fn identity(x) { x }\nidentity(1)\n";
        let (state, uri) = project.open("main.hern", source);

        let callee =
            hover(&state, uri.clone(), Position::new(1, 1)).expect("callee hover should resolve");
        let call = hover(&state, uri, Position::new(1, 10)).expect("call hover should resolve");

        assert_eq!(hover_text(callee), "fn(f64) -> f64");
        assert_eq!(hover_text(call), "f64");
    }

    #[test]
    fn hover_shows_callee_type_for_constrained_function_call() {
        // `sum` uses a `for` loop, giving it an `Iterable` constraint. The constrained
        // call path in the inferencer must still record the callee's type in symbol_types
        // so that hovering the callee shows the function type rather than the call result.
        let project = TestProject::new("constrained-callee-hover");
        let source = concat!(
            "fn sum(xs) {\n",
            "  let mut acc = 0;\n",
            "  for x in xs { acc = acc + x; }\n",
            "  acc\n",
            "}\n",
            "sum([1, 2, 3])\n",
        );
        let (state, uri) = project.open("main.hern", source);

        // Hover on "sum" in `sum([1, 2, 3])` — col 1 is the 's'
        let callee =
            hover(&state, uri.clone(), Position::new(5, 1)).expect("callee hover should resolve");
        // Hover on the call result — past the closing paren
        let call =
            hover(&state, uri, Position::new(5, 5)).expect("call result hover should resolve");

        let callee_text = hover_text(callee);
        // The callee type should be the function, not the return value ()
        assert!(
            callee_text.contains("fn("),
            "expected function type, got: {callee_text}"
        );
        assert!(
            callee_text.contains("Constraints:\n- 'a: Iterable"),
            "expected constraints section, got: {callee_text}"
        );
        assert_eq!(hover_text(call), "f64");
    }

    #[test]
    fn hover_groups_multiple_constraints_by_type_variable() {
        let project = TestProject::new("multi-constraint-hover");
        let source = concat!(
            "trait ConstraintA 'a {\n",
            "  fn a(x: 'a) -> 'a\n",
            "}\n",
            "trait ConstraintB 'a {\n",
            "  fn b(x: 'a) -> 'a\n",
            "}\n",
            "fn both ['a: ConstraintA + ConstraintB](x: 'a) -> 'a { x }\n",
        );
        let (state, uri) = project.open("main.hern", source);

        let info = hover(&state, uri, Position::new(6, 3)).expect("hover should resolve");

        assert_eq!(
            hover_text(info),
            "fn('a) -> 'a\n\nConstraints:\n- 'a: ConstraintA + ConstraintB"
        );
    }

    #[test]
    fn hover_returns_signature_for_function_declaration_name() {
        let project = TestProject::new("fn-declaration-hover");
        let source = "fn identity(x) { x }\nidentity(1)\n";
        let (state, uri) = project.open("main.hern", source);

        let info = hover(&state, uri, Position::new(0, 3)).expect("hover should resolve");

        let text = hover_text(info);
        assert_eq!(text, "fn('a) -> 'a");
    }

    #[test]
    fn hover_returns_type_for_let_declaration_name() {
        let project = TestProject::new("let-declaration-hover");
        let source = "let value = 1;\nvalue\n";
        let (state, uri) = project.open("main.hern", source);

        let info = hover(&state, uri, Position::new(0, 4)).expect("hover should resolve");

        assert_eq!(hover_text(info), "f64");
    }

    #[test]
    fn hover_returns_type_for_assignment_lvalue() {
        let project = TestProject::new("assignment-lvalue-hover");
        let source = "let mut value = 1;\nvalue = 2;\n";
        let (state, uri) = project.open("main.hern", source);

        let info = hover(&state, uri, Position::new(1, 1)).expect("hover should resolve");

        assert_eq!(hover_text(info), "f64");
    }

    #[test]
    fn hover_returns_element_type_for_for_loop_binding() {
        let project = TestProject::new("for-binding-hover");
        let source = concat!(
            "fn sum(steps) {\n",
            "  for step in steps {\n",
            "    step + 1\n",
            "  }\n",
            "}\n",
            "sum([1, 2])\n",
        );
        let (state, uri) = project.open("main.hern", source);

        let info = hover(&state, uri, Position::new(1, 6)).expect("hover should resolve");

        assert_eq!(hover_text(info), "f64");
    }

    #[test]
    fn hover_returns_binding_type_inside_structured_for_pattern() {
        let project = TestProject::new("for-pattern-hover");
        let source = concat!(
            "fn total(pairs) {\n",
            "  for (x, y) in pairs {\n",
            "    x + y + 1\n",
            "  }\n",
            "}\n",
            "total([(1, 2)])\n",
        );
        let (state, uri) = project.open("main.hern", source);

        let x_info = hover(&state, uri.clone(), Position::new(1, 7)).expect("hover should resolve");
        let y_info = hover(&state, uri, Position::new(1, 10)).expect("hover should resolve");

        assert_eq!(hover_text(x_info), "f64");
        assert_eq!(hover_text(y_info), "f64");
    }

    #[test]
    fn hover_returns_field_type_inside_record_for_pattern() {
        let project = TestProject::new("for-record-pattern-hover");
        let source = concat!(
            "fn total(rows) {\n",
            "  for #{ a, .. } in rows {\n",
            "    a + 1\n",
            "  }\n",
            "}\n",
            "total([#{ a: 1, b: 2 }])\n",
        );
        let (state, uri) = project.open("main.hern", source);

        let info = hover(&state, uri, Position::new(1, 9)).expect("hover should resolve");

        assert_eq!(hover_text(info), "f64");
    }

    #[test]
    fn hover_returns_type_for_plain_function_parameter() {
        // `x + 1` with the literal `1 :: f64` forces `x` to be `f64`,
        // so the parameter type is fully concrete and hover shows it directly.
        let project = TestProject::new("fn-param-hover");
        let source = "fn add_one(x) { x + 1 }\nadd_one(1)\n";
        let (state, uri) = project.open("main.hern", source);

        // "fn add_one(" = 11 chars; `x` is at col 11 on line 0.
        let info = hover(&state, uri, Position::new(0, 11)).expect("hover should resolve");

        assert_eq!(hover_text(info), "f64");
    }

    #[test]
    fn hover_returns_payload_type_for_match_some_binding() {
        // Hover on the `v` binding inside `Some(v)` in a match arm.
        let project = TestProject::new("match-some-hover");
        let source = concat!(
            "fn wrap(x) { Some(x) }\n", // line 0
            "match wrap(1) {\n",        // line 1
            "  Some(v) -> v + 1,\n",    // line 2: `v` at col 7
            "  None -> 0,\n",           // line 3
            "}\n",                      // line 4
        );
        let (state, uri) = project.open("main.hern", source);

        let info = hover(&state, uri, Position::new(2, 7)).expect("hover should resolve");

        assert_eq!(hover_text(info), "f64");
    }

    #[test]
    fn hover_returns_correct_type_for_match_ok_and_err_bindings() {
        // `Ok(v)` should give the first Result type argument (f64),
        // `Err(e)` should give the *second* type argument (string) — this validates
        // that the variant-env lookup picks the right type param, not always args[0].
        let project = TestProject::new("match-result-hover");
        let source = concat!(
            "fn safe_div(a, b) {\n",                             // line 0
            "  if b == 0 { Err(\"bad\") } else { Ok(a / b) }\n", // line 1
            "}\n",                                               // line 2
            "match safe_div(10, 2) {\n",                         // line 3
            "  Ok(v) -> v,\n",                                   // line 4: `v` at col 5
            "  Err(e) -> 0,\n",                                  // line 5: `e` at col 6
            "}\n",                                               // line 6
        );
        let (state, uri) = project.open("main.hern", source);

        let ok_info =
            hover(&state, uri.clone(), Position::new(4, 5)).expect("Ok hover should resolve");
        let err_info = hover(&state, uri, Position::new(5, 6)).expect("Err hover should resolve");

        assert_eq!(hover_text(ok_info), "f64");
        assert_eq!(hover_text(err_info), "string");
    }

    #[test]
    fn hover_resolves_constructor_payload_type_aliases() {
        let project = TestProject::new("match-aliased-payload-hover");
        let source = concat!(
            "type Amount = f64\n",
            "type Wrapped = Wrap(Amount) | Empty\n",
            "match Wrap(1) {\n",
            "  Wrap(v) -> v + 1,\n",
            "  Empty -> 0,\n",
            "}\n",
        );
        let (state, uri) = project.open("main.hern", source);

        let info = hover(&state, uri, Position::new(3, 7)).expect("hover should resolve");

        assert_eq!(hover_text(info), "f64");
    }

    #[test]
    fn hover_returns_imported_member_signature() {
        let source = "let dep = import \"dep\";\ndep.value()\n";
        let ImportFixture {
            state, entry_uri, ..
        } = import_fixture(
            "imported-member-hover",
            source,
            "fn value() { 1 }\n#{ value: value }\n",
        );

        let info = hover(&state, entry_uri, Position::new(1, 5)).expect("hover should resolve");

        assert_eq!(hover_text(info), "dep.value: fn() -> f64");
    }

    #[test]
    fn hover_plain_text_fallback_preserves_content() {
        let project = TestProject::new("hover-plain-text");
        let source = "fn id(x) { x }\nid(1)\n";
        let (mut state, uri) = project.open("main.hern", source);
        state.supports_markdown_hover = false;

        let info = hover(&state, uri, Position::new(1, 1)).expect("hover should resolve");

        assert_eq!(hover_text(info), "fn(f64) -> f64");
    }

    #[test]
    fn diagnostics_cache_successful_analysis_for_hover_reuse() {
        let project = TestProject::new("analysis-cache");
        let source = "let value = 1;\nvalue\n";
        let (mut state, uri) = project.open("main.hern", source);

        assert!(state.cached_analyses.is_empty());
        let diagnostics = diagnostics_for_document(&mut state, &uri);

        assert!(diagnostics[&uri].is_empty());
        assert!(state.cached_analyses.contains_key(&uri));
        let info = hover(&state, uri, Position::new(1, 1)).expect("hover should resolve");
        assert_eq!(hover_text(info), "f64");
    }

    #[test]
    fn diagnostics_do_not_cache_partial_analysis() {
        let project = TestProject::new("analysis-cache-diagnostics");
        let source = "let value: bool = 1;\nvalue\n";
        let (mut state, uri) = project.open("main.hern", source);

        let diagnostics = diagnostics_for_document(&mut state, &uri);

        assert_eq!(diagnostics[&uri].len(), 1);
        assert!(state.cached_analyses.is_empty());
    }

    #[test]
    fn document_change_invalidates_cached_analysis() {
        let project = TestProject::new("analysis-cache-invalidated");
        let source = "let value = 1;\nvalue\n";
        let (mut state, uri) = project.open("main.hern", source);

        diagnostics_for_document(&mut state, &uri);

        assert!(state.cached_analyses.contains_key(&uri));
        state.set_document(uri.clone(), "let value = 2;\nvalue\n".to_string(), 1);

        assert!(state.cached_analyses.is_empty());
        assert_eq!(state.document_versions[&uri], 1);
    }

    #[test]
    fn definition_resolves_top_level_symbol_in_same_module() {
        let project = TestProject::new("definition-top-level");
        let source = "fn value() { 1 }\nvalue()\n";
        let (state, uri) = project.open("main.hern", source);

        let location = definition(&state, uri.clone(), Position::new(1, 1))
            .expect("definition should resolve");

        assert_eq!(location.uri, uri);
        assert_eq!(location.range.start, Position::new(0, 3));
    }

    #[test]
    fn definition_resolves_local_symbol_in_same_module() {
        let project = TestProject::new("definition-local");
        let source = "{ let value = 1; value }\n";
        let (state, uri) = project.open("main.hern", source);

        let location = definition(&state, uri.clone(), Position::new(0, 18))
            .expect("definition should resolve");

        assert_eq!(location.uri, uri);
        assert_eq!(location.range.start, Position::new(0, 6));
    }

    #[test]
    fn definition_resolves_imported_member_symbol() {
        let source = "let dep = import \"dep\";\ndep.value()\n";
        let ImportFixture {
            state,
            entry_uri,
            dep_uri,
        } = import_fixture(
            "definition-import",
            source,
            "fn value() { 1 }\n#{ value: value }\n",
        );
        let location =
            definition(&state, entry_uri, Position::new(1, 5)).expect("definition should resolve");

        assert_eq!(location.uri, dep_uri);
        assert_eq!(location.range.start, Position::new(0, 3));
    }

    #[test]
    fn references_returns_same_module_uses_without_declaration() {
        let project = TestProject::new("references-local");
        let source = "let value = 1;\nvalue\nvalue\n";
        let (state, uri) = project.open("main.hern", source);

        let locs = references(&state, uri.clone(), Position::new(0, 4), false);

        // two uses on lines 2 and 3; declaration on line 1 is excluded
        assert_eq!(locs.len(), 2);
        assert!(locs.iter().all(|l| l.uri == uri));
        assert_eq!(locs[0].range.start.line, 1);
        assert_eq!(locs[1].range.start.line, 2);
    }

    #[test]
    fn references_honors_include_declaration_true() {
        let project = TestProject::new("references-include-decl");
        let source = "fn value() { 1 }\nvalue()\n";
        let (state, uri) = project.open("main.hern", source);

        let locs = references(&state, uri.clone(), Position::new(1, 1), true);

        // declaration (line 1) + use (line 2)
        assert_eq!(locs.len(), 2);
        assert_eq!(locs[0].range.start.line, 0);
        assert_eq!(locs[1].range.start.line, 1);
    }

    #[test]
    fn references_returns_empty_for_unknown_position() {
        let project = TestProject::new("references-empty");
        let source = "let value = 1;\n";
        let (state, uri) = project.open("main.hern", source);

        let locs = references(&state, uri, Position::new(99, 0), false);

        assert!(locs.is_empty());
    }

    #[test]
    fn references_returns_imported_member_uses() {
        let source = "let dep = import \"dep\";\ndep.value\ndep.value\n";
        let ImportFixture {
            state, entry_uri, ..
        } = import_fixture(
            "references-import-member",
            source,
            "fn value() { 1 }\n#{ value: value }\n",
        );
        let locs = references(&state, entry_uri.clone(), Position::new(1, 4), false);

        assert_eq!(locs.len(), 2);
        assert!(locs.iter().all(|l| l.uri == entry_uri));
    }

    #[test]
    fn document_highlights_mark_declaration_write_and_uses_read() {
        use lsp_types::DocumentHighlightKind;
        let project = TestProject::new("document-highlights-local");
        let source = "let value = 1;\nvalue\nvalue\n";
        let (state, uri) = project.open("main.hern", source);

        let highlights = document_highlights(&state, uri, Position::new(1, 1));

        assert_eq!(highlights.len(), 3);
        assert_eq!(highlights[0].kind, Some(DocumentHighlightKind::WRITE));
        assert_eq!(highlights[0].range.start, Position::new(0, 4));
        assert_eq!(highlights[1].kind, Some(DocumentHighlightKind::READ));
        assert_eq!(highlights[2].kind, Some(DocumentHighlightKind::READ));
    }

    #[test]
    fn document_highlights_respect_shadowing() {
        let project = TestProject::new("document-highlights-shadow");
        let source = "let value = 1;\n{ let value = 2; value };\nvalue\n";
        let (state, uri) = project.open("main.hern", source);

        let inner = document_highlights(&state, uri.clone(), Position::new(1, 17));
        let outer = document_highlights(&state, uri, Position::new(2, 1));

        assert_eq!(inner.len(), 2);
        assert!(inner.iter().all(|item| item.range.start.line == 1));
        assert_eq!(outer.len(), 2);
        assert!(
            outer
                .iter()
                .all(|item| item.range.start.line == 0 || item.range.start.line == 2)
        );
    }

    #[test]
    fn document_highlights_imported_member_uses_in_current_document() {
        use lsp_types::DocumentHighlightKind;
        let source = "let dep = import \"dep\";\ndep.value\ndep.value\n";
        let ImportFixture {
            state, entry_uri, ..
        } = import_fixture(
            "document-highlights-import",
            source,
            "fn value() { 1 }\n#{ value: value }\n",
        );

        let highlights = document_highlights(&state, entry_uri, Position::new(1, 4));

        assert_eq!(highlights.len(), 2);
        assert!(
            highlights
                .iter()
                .all(|item| item.kind == Some(DocumentHighlightKind::READ))
        );
    }

    #[test]
    fn references_imported_member_include_declaration_adds_target_definition() {
        let source = "let dep = import \"dep\";\ndep.value\n";
        let ImportFixture {
            state,
            entry_uri,
            dep_uri,
        } = import_fixture(
            "references-import-decl",
            source,
            "fn value() { 1 }\n#{ value: value }\n",
        );
        let locs = references(&state, entry_uri.clone(), Position::new(1, 4), true);

        assert_eq!(locs.len(), 2);
        assert!(locs.iter().any(|l| l.uri == dep_uri));
        assert!(locs.iter().any(|l| l.uri == entry_uri));
    }

    #[test]
    fn unsaved_overlay_changes_diagnostics_without_disk_write() {
        let project = TestProject::new("overlay-diagnostics");
        let uri = project.write("main.hern", "let value = 1;\n");
        let mut state = state_with_document(uri.clone(), "let a = ;\nlet b = ;\n".to_string());
        let diagnostics = diagnostics_for_document(&mut state, &uri);
        let entry_diagnostics = diagnostics
            .get(&uri)
            .expect("overlay parse diagnostics should target entry");

        assert_eq!(entry_diagnostics.len(), 2);
    }

    #[test]
    fn new_unsaved_file_gets_full_analysis_from_open_buffer() {
        let project = TestProject::new("new-unsaved-file");
        let path = project.root.join("main.hern");
        let uri = path_to_uri(&path).expect("test URI should encode");
        let source = "let value = 1;\nvalue\n";
        let mut state = state_with_document(uri.clone(), source.to_string());

        let diagnostics = diagnostics_for_document(&mut state, &uri);
        let info = hover(&state, uri.clone(), Position::new(1, 1)).expect("hover should resolve");
        let items = completion(&state, uri, Position::new(1, 1));

        assert!(
            !path.exists(),
            "test must exercise a file that has not been saved to disk"
        );
        assert!(diagnostics.values().all(Vec::is_empty));
        assert_eq!(hover_text(info), "f64");
        assert!(
            items
                .iter()
                .any(|item| completion_insert_name(item) == "value"),
            "completion should use the open unsaved buffer"
        );
    }

    #[test]
    fn new_unsaved_file_can_import_another_open_unsaved_file() {
        let project = TestProject::new("new-unsaved-import");
        let entry_path = project.root.join("main.hern");
        let dep_path = project.root.join("dep.hern");
        let entry_uri = path_to_uri(&entry_path).expect("entry URI should encode");
        let dep_uri = path_to_uri(&dep_path).expect("dep URI should encode");
        let mut state = state_with_document(
            entry_uri.clone(),
            "let dep = import \"dep\";\ndep.value\n".to_string(),
        );
        state.set_document(dep_uri.clone(), "#{ value: 1 }\n".to_string(), 0);

        let diagnostics = diagnostics_for_document(&mut state, &entry_uri);
        let info =
            hover(&state, entry_uri, Position::new(1, 5)).expect("import hover should resolve");

        assert!(!entry_path.exists());
        assert!(!dep_path.exists());
        assert!(diagnostics.values().all(Vec::is_empty));
        assert_eq!(hover_text(info), "dep.value: f64");
    }

    #[test]
    fn type_mismatch_diagnostic_has_nonzero_range() {
        let project = TestProject::new("type-range");
        let source = "let value: bool = 1;\n";
        let (mut state, uri) = project.open("main.hern", source);

        let diagnostics = diagnostics_for_document(&mut state, &uri);
        let diagnostic = diagnostics
            .values()
            .flat_map(|items| items.iter())
            .next()
            .expect("type diagnostic should be reported");

        assert!(diagnostic.range.end.character > diagnostic.range.start.character);
    }

    #[test]
    fn rename_local_let_edits_declaration_and_use() {
        let project = TestProject::new("rename-local-let");
        let source = "{ let value = 1; value }\n";
        let (state, uri) = project.open("main.hern", source);

        let edit = rename(
            &state,
            uri.clone(),
            Position::new(0, 6),
            "amount".to_string(),
        )
        .expect("rename should succeed")
        .expect("rename should return edits");

        let edits = edit.changes.expect("changes should be present");
        let file_edits = edits.get(&uri).expect("edits for file should be present");
        assert_eq!(file_edits.len(), 2);
        assert!(file_edits.iter().all(|e| e.new_text == "amount"));
        // declaration before use in source order
        assert!(file_edits[0].range.start < file_edits[1].range.start);
    }

    #[test]
    fn prepare_rename_local_let_returns_current_identifier_range() {
        use lsp_types::PrepareRenameResponse;
        let project = TestProject::new("prepare-rename-local-let");
        let source = "{ let value = 1; value }\n";
        let (state, uri) = project.open("main.hern", source);

        let declaration = prepare_rename(&state, uri.clone(), Position::new(0, 6))
            .expect("prepare rename should not error")
            .expect("declaration should be renameable");
        let reference = prepare_rename(&state, uri, Position::new(0, 17))
            .expect("prepare rename should not error")
            .expect("reference should be renameable");

        assert_eq!(
            declaration,
            PrepareRenameResponse::Range(Range::new(Position::new(0, 6), Position::new(0, 11)))
        );
        assert_eq!(
            reference,
            PrepareRenameResponse::Range(Range::new(Position::new(0, 17), Position::new(0, 22)))
        );
    }

    #[test]
    fn rename_function_edits_declaration_and_call() {
        let project = TestProject::new("rename-fn");
        let source = "fn value() { 1 }\nvalue()\n";
        let (state, uri) = project.open("main.hern", source);

        let edit = rename(
            &state,
            uri.clone(),
            Position::new(1, 1),
            "compute".to_string(),
        )
        .expect("rename should succeed")
        .expect("rename should return edits");

        let edits = edit.changes.expect("changes should be present");
        let file_edits = edits.get(&uri).expect("edits for file should be present");
        assert_eq!(file_edits.len(), 2);
        assert!(file_edits.iter().all(|e| e.new_text == "compute"));
        assert_eq!(file_edits[0].range.start.line, 0); // declaration
        assert_eq!(file_edits[1].range.start.line, 1); // call
    }

    #[test]
    fn rename_respects_shadowing_inner() {
        let project = TestProject::new("rename-shadow-inner");
        let source = "let value = 1;\n{ let value = 2; value };\nvalue\n";
        let (state, uri) = project.open("main.hern", source);

        let edit = rename(
            &state,
            uri.clone(),
            Position::new(1, 17),
            "inner".to_string(),
        )
        .expect("rename should succeed")
        .expect("rename should return edits");

        let edits = edit.changes.expect("changes should be present");
        let file_edits = edits.get(&uri).expect("edits for file should be present");
        // only inner declaration and inner use — both on line 2 (0-indexed line 1)
        assert_eq!(file_edits.len(), 2);
        assert!(file_edits.iter().all(|e| e.range.start.line == 1));
    }

    #[test]
    fn rename_respects_shadowing_outer() {
        let project = TestProject::new("rename-shadow-outer");
        let source = "let value = 1;\n{ let value = 2; value };\nvalue\n";
        let (state, uri) = project.open("main.hern", source);

        let edit = rename(
            &state,
            uri.clone(),
            Position::new(0, 4),
            "outer".to_string(),
        )
        .expect("rename should succeed")
        .expect("rename should return edits");

        let edits = edit.changes.expect("changes should be present");
        let file_edits = edits.get(&uri).expect("edits for file should be present");
        // outer declaration (line 1) and outer use (line 3); inner binding is separate
        assert_eq!(file_edits.len(), 2);
        assert!(
            file_edits
                .iter()
                .all(|e| e.range.start.line == 0 || e.range.start.line == 2)
        );
    }

    #[test]
    fn rename_cursor_not_on_symbol_returns_none() {
        let project = TestProject::new("rename-no-symbol");
        let source = "let value = 1;\n";
        let (state, uri) = project.open("main.hern", source);

        let result = rename(&state, uri, Position::new(0, 10), "x".to_string())
            .expect("rename should not error");

        assert!(result.is_none());
    }

    #[test]
    fn rename_invalid_name_returns_error() {
        let project = TestProject::new("rename-invalid");
        let source = "let value = 1;\n";
        let (state, uri) = project.open("main.hern", source);

        assert!(rename(&state, uri.clone(), Position::new(0, 4), "1bad".to_string()).is_err());
        assert!(rename(&state, uri.clone(), Position::new(0, 4), "let".to_string()).is_err());
        assert!(rename(&state, uri.clone(), Position::new(0, 4), String::new()).is_err());
    }

    #[test]
    fn rename_imported_member_returns_error() {
        let source = "let dep = import \"dep\";\ndep.value\n";
        let ImportFixture {
            state, entry_uri, ..
        } = import_fixture(
            "rename-import-member",
            source,
            "fn value() { 1 }\n#{ value: value }\n",
        );
        let result = rename(
            &state,
            entry_uri,
            Position::new(1, 4),
            "renamed".to_string(),
        );

        assert!(result.is_err());
    }

    #[test]
    fn prepare_rename_imported_member_returns_error() {
        let source = "let dep = import \"dep\";\ndep.value\n";
        let ImportFixture {
            state, entry_uri, ..
        } = import_fixture(
            "prepare-rename-import-member",
            source,
            "fn value() { 1 }\n#{ value: value }\n",
        );

        let result = prepare_rename(&state, entry_uri, Position::new(1, 4));

        assert!(result.is_err());
    }

    #[test]
    fn rename_type_definition_returns_error() {
        let project = TestProject::new("rename-type");
        let source = "type Option('a) = None | Some('a)\n";
        let (state, uri) = project.open("main.hern", source);

        let result = rename(&state, uri, Position::new(0, 5), "Maybe".to_string());

        assert!(result.is_err());
    }

    #[test]
    fn prepare_rename_type_definition_returns_error() {
        let project = TestProject::new("prepare-rename-type");
        let source = "type Option('a) = None | Some('a)\n";
        let (state, uri) = project.open("main.hern", source);

        let result = prepare_rename(&state, uri, Position::new(0, 5));

        assert!(result.is_err());
    }

    #[test]
    fn completion_returns_top_level_names() {
        let project = TestProject::new("completion-top-level");
        let source = "fn greet() { 1 }\nlet count = 42;\ngreet()\n";
        let (state, uri) = project.open("main.hern", source);

        let items = completion(&state, uri, Position::new(2, 1));

        let names: Vec<_> = items.iter().map(completion_insert_name).collect();
        assert!(
            names.contains(&"greet"),
            "greet should be a completion candidate"
        );
        assert!(
            names.contains(&"count"),
            "count should be a completion candidate"
        );
    }

    #[test]
    fn instrumentation_is_disabled_by_default() {
        let state = ServerState::new().expect("server state should initialize");

        assert!(!state.config.debug_timing);
        assert_eq!(state.perf.cache_hits.get(), 0);
        assert_eq!(state.perf.cache_misses.get(), 0);
    }

    #[test]
    fn debug_timing_does_not_change_completion_results() {
        let project = TestProject::new("completion-timing");
        let source = "fn greet() { 1 }\nlet count = 42;\ngreet()\n";
        let (state, uri) = project.open("main.hern", source);
        let mut timed_state = state_with_document(uri.clone(), source.to_string());
        timed_state.config.debug_timing = true;

        let plain = completion(&state, uri.clone(), Position::new(2, 1));
        let timed = completion(&timed_state, uri, Position::new(2, 1));

        assert_eq!(
            plain.iter().map(completion_insert_name).collect::<Vec<_>>(),
            timed.iter().map(completion_insert_name).collect::<Vec<_>>()
        );
    }

    #[test]
    fn completion_returns_block_local_inside_scope() {
        let project = TestProject::new("completion-block-local");
        let source = "fn run() { let total = 1; total }\n";
        let (state, uri) = project.open("main.hern", source);

        let items = completion(&state, uri, Position::new(0, 26));

        let names: Vec<_> = items.iter().map(completion_insert_name).collect();
        assert!(names.contains(&"total"), "total should be in scope");
        assert!(
            names.contains(&"run"),
            "run should be in scope as a top-level fn"
        );
    }

    #[test]
    fn completion_shadowing_returns_inner_binding() {
        use lsp_types::CompletionItemKind;
        let project = TestProject::new("completion-shadow");
        let source = "let x = 1;\n{ let x = 2; x }\n";
        let (state, uri) = project.open("main.hern", source);

        let items = completion(&state, uri, Position::new(1, 13));

        let x_items: Vec<_> = items
            .iter()
            .filter(|i| completion_insert_name(i) == "x")
            .collect();
        assert_eq!(
            x_items.len(),
            1,
            "exactly one `x` candidate (inner shadows outer)"
        );
        // inner `x` is a VARIABLE (Local), outer top-level would also be VARIABLE so both map the same
        assert_eq!(x_items[0].kind, Some(CompletionItemKind::VARIABLE));
    }

    #[test]
    fn completion_import_binding_has_module_kind() {
        use lsp_types::CompletionItemKind;
        let source = "let dep = import \"dep\";\ndep\n";
        let ImportFixture {
            state, entry_uri, ..
        } = import_fixture(
            "completion-import-binding",
            source,
            "fn value() { 1 }\n#{ value: value }\n",
        );

        let items = completion(&state, entry_uri, Position::new(1, 0));

        let dep_item = items
            .iter()
            .find(|i| completion_insert_name(i) == "dep")
            .expect("dep binding should appear in completion");
        assert_eq!(dep_item.kind, Some(CompletionItemKind::MODULE));
    }

    #[test]
    fn completion_suggests_import_paths_inside_import_string() {
        use lsp_types::CompletionItemKind;
        let project = TestProject::new("completion-import-path");
        let uri = project.write("main.hern", "let dep = import \"de\";\n");
        project.write("dep.hern", "#{ value: 1 }\n");
        project.write("other.hern", "#{ value: 2 }\n");
        let state = state_with_document(uri.clone(), "let dep = import \"de\";\n".to_string());

        let items = completion(&state, uri, Position::new(0, 20));

        assert!(
            items.iter().any(|item| item.label == "dep"
                && item.kind == Some(CompletionItemKind::FILE)
                && item.detail.as_deref() == Some("local module")),
            "expected dep.hern import completion, got {:?}",
            items
        );
        assert!(!items.iter().any(|item| item.label == "other"));
    }

    #[test]
    fn completion_suggests_imported_module_members_after_dot() {
        use lsp_types::CompletionItemKind;
        let source = "let dep = import \"dep\";\ndep.\n";
        let ImportFixture {
            state, entry_uri, ..
        } = import_fixture(
            "completion-import-member",
            source,
            "#{ value: 1, name: \"hern\" }\n",
        );

        let items = completion(&state, entry_uri, Position::new(1, 4));

        let names: Vec<_> = items.iter().map(completion_insert_name).collect();
        assert!(
            names.contains(&"value"),
            "expected value member: {:?}",
            names
        );
        assert!(names.contains(&"name"), "expected name member: {:?}", names);
        assert!(
            items
                .iter()
                .all(|item| item.kind == Some(CompletionItemKind::FIELD))
        );
    }

    #[test]
    fn completion_suggests_record_fields_after_dot() {
        use lsp_types::CompletionItemKind;
        let project = TestProject::new("completion-record-field");
        let source = "let point = #{ x: 1, y: 2 };\npoint.\n";
        let (state, uri) = project.open("main.hern", source);

        let items = completion(&state, uri, Position::new(1, 6));

        let names: Vec<_> = items.iter().map(completion_insert_name).collect();
        assert!(names.contains(&"x"), "expected x field: {names:?}");
        assert!(names.contains(&"y"), "expected y field: {names:?}");
        assert!(
            items
                .iter()
                .all(|item| item.kind == Some(CompletionItemKind::FIELD))
        );
    }

    #[test]
    fn completion_suggests_types_in_annotation_position() {
        use lsp_types::CompletionItemKind;
        let project = TestProject::new("completion-type-position");
        let source = "type Option('a) = None | Some('a)\ntrait Show 'a { fn show(x: 'a) -> string }\nlet value: O = 1;\n";
        let (state, uri) = project.open("main.hern", source);

        let items = completion(&state, uri, Position::new(2, 12));

        let option = items
            .iter()
            .find(|item| completion_insert_name(item) == "Option")
            .expect("Option should be suggested");
        assert_eq!(option.kind, Some(CompletionItemKind::STRUCT));
        assert!(
            items
                .iter()
                .any(|item| completion_insert_name(item) == "Show"
                    && item.kind == Some(CompletionItemKind::INTERFACE))
        );
    }

    #[test]
    fn completion_suppresses_scope_names_after_let_keyword() {
        let project = TestProject::new("completion-let-suppression");
        let source = "let existing = 1;\nlet \n";
        let (state, uri) = project.open("main.hern", source);

        let items = completion(&state, uri, Position::new(1, 4));

        assert!(items.is_empty());
    }

    #[test]
    fn completion_provides_type_detail_for_top_level_function() {
        let project = TestProject::new("completion-type-detail");
        let source = "fn double(x: f64) -> f64 { x + x }\ndouble(1)\n";
        let (state, uri) = project.open("main.hern", source);

        let items = completion(&state, uri, Position::new(1, 1));

        let double_item = items
            .iter()
            .find(|i| completion_insert_name(i) == "double")
            .expect("double should appear in completion");
        assert_eq!(double_item.label, "double");
        assert_eq!(double_item.insert_text.as_deref(), Some("double"));
        assert_eq!(double_item.detail.as_deref(), Some("fn(f64) -> f64"));
        assert_eq!(
            double_item
                .label_details
                .as_ref()
                .and_then(|details| details.detail.as_deref()),
            Some(": fn(f64) -> f64")
        );
    }

    #[test]
    fn completion_keeps_type_detail_during_partial_identifier_edit() {
        use lsp_types::{CompletionTextEdit, TextEdit};
        let project = TestProject::new("completion-partial-identifier-type-detail");
        let source = "fn double(x: f64) -> f64 { x + x }\ndo\n";
        let (state, uri) = project.open("main.hern", source);

        let items = completion(&state, uri, Position::new(1, 2));

        let double_item = items
            .iter()
            .find(|i| completion_insert_name(i) == "double")
            .expect("double should appear while a partial identifier is being typed");
        assert_eq!(double_item.label, "double");
        assert_eq!(double_item.detail.as_deref(), Some("fn(f64) -> f64"));
        assert_eq!(
            double_item.text_edit.as_ref(),
            Some(&CompletionTextEdit::Edit(TextEdit {
                range: Range::new(Position::new(1, 0), Position::new(1, 2)),
                new_text: "double".to_string(),
            }))
        );
    }

    #[test]
    fn completion_provides_type_detail_for_local_and_parameter() {
        let project = TestProject::new("completion-local-param-detail");
        let source = "fn run(x) { let local = x + 1; local }\nrun(1)\n";
        let (state, uri) = project.open("main.hern", source);

        let items = completion(&state, uri, Position::new(0, 34));

        let x_item = items
            .iter()
            .find(|i| completion_insert_name(i) == "x")
            .expect("parameter should appear in completion");
        let local_item = items
            .iter()
            .find(|i| completion_insert_name(i) == "local")
            .expect("local should appear in completion");

        assert_eq!(x_item.detail.as_deref(), Some("f64"));
        assert_eq!(local_item.detail.as_deref(), Some("f64"));
        assert_eq!(
            x_item
                .label_details
                .as_ref()
                .and_then(|details| details.detail.as_deref()),
            Some(": f64")
        );
        assert_eq!(
            local_item
                .label_details
                .as_ref()
                .and_then(|details| details.detail.as_deref()),
            Some(": f64")
        );
    }

    #[test]
    fn completion_formats_constrained_type_detail() {
        let project = TestProject::new("completion-constrained-detail");
        let source = concat!(
            "fn sum(xs) {\n",
            "  let mut acc = 0;\n",
            "  for x in xs { acc = acc + x; }\n",
            "  acc\n",
            "}\n",
            "\n",
        );
        let (state, uri) = project.open("main.hern", source);

        let items = completion(&state, uri, Position::new(5, 0));

        let sum_item = items
            .iter()
            .find(|i| completion_insert_name(i) == "sum")
            .expect("sum should appear in completion");
        assert_eq!(sum_item.detail.as_deref(), Some("fn('a(f64)) -> f64"));
        assert_eq!(
            sum_item
                .label_details
                .as_ref()
                .and_then(|details| details.detail.as_deref()),
            Some(": fn('a(f64)) -> f64")
        );
    }

    #[test]
    fn completion_parse_only_fallback_returns_names_on_type_error() {
        let project = TestProject::new("completion-parse-fallback");
        let source = "let bad: bool = 1;\nfn helper() { 1 }\nhelper()\n";
        let (state, uri) = project.open("main.hern", source);

        let items = completion(&state, uri, Position::new(2, 1));

        let names: Vec<_> = items.iter().map(completion_insert_name).collect();
        assert!(
            names.contains(&"helper"),
            "helper should appear even when inference fails"
        );
        assert!(
            names.contains(&"bad"),
            "bad should appear even when inference fails"
        );
    }

    #[test]
    fn completion_recovering_fallback_returns_names_on_syntax_error() {
        let project = TestProject::new("completion-recovering-fallback");
        let on_disk = "fn helper() { 1 }\nhelper()\n";
        let uri = project.write("main.hern", on_disk);

        let mid_edit = "fn helper() { 1 }\nfn broken(\n";
        let state = state_with_document(uri.clone(), mid_edit.to_string());

        let items = completion(&state, uri, Position::new(0, 5));

        let names: Vec<_> = items.iter().map(completion_insert_name).collect();
        assert!(
            names.contains(&"helper"),
            "helper should appear even when overlay has a syntax error; got {:?}",
            names
        );
    }

    #[test]
    fn completion_in_gap_between_let_and_for_shows_parameter_and_local() {
        let project = TestProject::new("completion-gap-let-for");
        let source = concat!(
            "fn sum(steps) {\n",
            "  let mut total = 0;\n",
            "\n",
            "  for step in steps {\n",
            "    total = total + step;\n",
            "  }\n",
            "\n",
            "  total\n",
            "}\n",
        );
        let uri = project.write("main.hern", source);

        let with_edit = concat!(
            "fn sum(steps) {\n",
            "  let mut total = 0;\n",
            "  t\n",
            "  for step in steps {\n",
            "    total = total + step;\n",
            "  }\n",
            "\n",
            "  total\n",
            "}\n",
        );
        let state = state_with_document(uri.clone(), with_edit.to_string());

        let items = completion(&state, uri, Position::new(2, 3));
        let names: Vec<_> = items.iter().map(completion_insert_name).collect();

        assert!(
            names.contains(&"total"),
            "`total` should be visible at the gap; got {:?}",
            names
        );
        assert!(
            names.contains(&"steps"),
            "`steps` should be visible at the gap; got {:?}",
            names
        );
    }

    // --- Workspace tracking tests ---

    #[test]
    fn entries_affected_excludes_dep_only_uri_from_self() {
        let ImportFixture {
            mut state,
            entry_uri,
            dep_uri,
        } = import_fixture(
            "affected-dep-only",
            "let dep = import \"dep\";\ndep.value\n",
            "#{ value: 1 }\n",
        );
        diagnostics_for_document(&mut state, &entry_uri);

        let affected = state.entries_affected_by_document(&dep_uri);
        assert!(
            affected.contains(&entry_uri),
            "owning entry should be in affected set"
        );
        assert!(
            !affected.contains(&dep_uri),
            "dep-only URI should not be in its own affected set"
        );
    }

    #[test]
    fn entries_affected_includes_open_entry_uri_itself() {
        let project = TestProject::new("affected-open-entry");
        let (state, uri) = project.open("main.hern", "let value = 1;\n");

        let affected = state.entries_affected_by_document(&uri);
        assert!(
            affected.contains(&uri),
            "open entry URI should be in its own affected set"
        );
    }

    #[test]
    fn closing_dep_only_does_not_clear_entry_diagnostics_for_dep() {
        let ImportFixture {
            mut state,
            entry_uri,
            dep_uri,
        } = import_fixture(
            "close-dep-only-diagnostics",
            "let dep = import \"dep\";\ndep.value\n",
            "#{ value: 1 }\n",
        );
        assert!(diagnostics_for_document(&mut state, &entry_uri)[&entry_uri].is_empty());

        state.set_document(dep_uri.clone(), "let broken = ;\n".to_string(), 1);
        let dep_diags = diagnostics_for_document(&mut state, &entry_uri);
        assert_eq!(
            dep_diags
                .get(&dep_uri)
                .expect("dep should have errors")
                .len(),
            1,
            "dep should have one error before close"
        );

        assert!(
            !state.is_open_entry(&dep_uri),
            "dep added via set_document only should not be an open entry"
        );

        state.unmark_open_entry(&dep_uri);
        state.remove_document(&dep_uri);

        assert!(
            state.entry_dependencies.contains_key(&entry_uri),
            "entry's dependency tracking should be intact after dep-only close"
        );
    }

    #[test]
    fn closing_entry_clears_its_own_diagnostics_but_not_other_entry_contributions() {
        // When entry_a is closed, its diagnostics_by_entry slot should be removable
        // without affecting entry_b's contributions to the same dep.
        let dep = uri("file:///workspace/dep.hern");
        let entry_a = uri("file:///workspace/a.hern");
        let entry_b = uri("file:///workspace/b.hern");

        let mut state = ServerState::new().expect("server state should initialize");
        state.open_entry_uris.insert(entry_a.clone());
        state.open_entry_uris.insert(entry_b.clone());
        state.diagnostics_by_entry.insert(
            entry_a.clone(),
            HashMap::from([(dep.clone(), vec![diagnostic("error from a")])]),
        );
        state.diagnostics_by_entry.insert(
            entry_b.clone(),
            HashMap::from([(dep.clone(), vec![diagnostic("error from b")])]),
        );
        state.entry_dependencies.insert(
            entry_a.clone(),
            HashSet::from([entry_a.clone(), dep.clone()]),
        );

        // Closing entry_a: remove its slot. entry_b's contribution should survive.
        state.diagnostics_by_entry.remove(&entry_a);
        state.remove_entry_tracking(&entry_a);
        state.unmark_open_entry(&entry_a);

        let combined = combined_diagnostics_for_uri(&state, &dep);
        assert_eq!(combined.len(), 1);
        assert_eq!(combined[0].message, "error from b");
    }

    #[test]
    fn entry_stops_importing_dep_stale_diagnostics_disappear() {
        let ImportFixture {
            mut state,
            entry_uri,
            dep_uri,
        } = import_fixture(
            "stale-dep-diag",
            "let dep = import \"dep\";\ndep.value\n",
            "let broken = ;\n",
        );

        let first = diagnostics_for_document(&mut state, &entry_uri);
        assert!(
            first.get(&dep_uri).is_some_and(|d| !d.is_empty()),
            "dep errors should appear initially"
        );

        state.set_document(entry_uri.clone(), "let value = 42;\n".to_string(), 1);
        let second = diagnostics_for_document(&mut state, &entry_uri);

        assert!(
            second.get(&dep_uri).is_none_or(|d| d.is_empty()),
            "stale dep diagnostics should be gone after entry stops importing dep"
        );
    }

    #[test]
    fn imported_dep_edit_updates_hover_after_revalidation() {
        let ImportFixture {
            mut state,
            entry_uri,
            dep_uri,
        } = import_fixture(
            "dep-edit-hover",
            "let dep = import \"dep\";\ndep.value\n",
            "#{ value: 1 }\n",
        );

        assert!(diagnostics_for_document(&mut state, &entry_uri)[&entry_uri].is_empty());
        assert!(state::cached_analysis(&state, &entry_uri).is_some());

        state.set_document(dep_uri, "#{ value: \"hello\" }\n".to_string(), 1);
        assert!(state::cached_analysis(&state, &entry_uri).is_none());

        assert!(diagnostics_for_document(&mut state, &entry_uri)[&entry_uri].is_empty());

        let info = hover(&state, entry_uri, Position::new(1, 5)).expect("hover should resolve");
        assert_eq!(
            hover_text(info),
            "dep.value: string",
            "hover should reflect the updated dep type"
        );
    }

    #[test]
    fn imported_dep_edit_updates_definition_after_revalidation() {
        let ImportFixture {
            mut state,
            entry_uri,
            dep_uri,
        } = import_fixture(
            "dep-edit-definition",
            "let dep = import \"dep\";\ndep.value()\n",
            "fn value() { 1 }\n#{ value: value }\n",
        );

        assert!(diagnostics_for_document(&mut state, &entry_uri)[&entry_uri].is_empty());

        state.set_document(
            dep_uri.clone(),
            "fn value() { \"hello\" }\n#{ value: value }\n".to_string(),
            1,
        );
        assert!(diagnostics_for_document(&mut state, &entry_uri)[&entry_uri].is_empty());

        let loc = definition(&state, entry_uri, Position::new(1, 5))
            .expect("definition should resolve after dep overlay");
        assert_eq!(
            loc.uri, dep_uri,
            "definition should point into the dep module"
        );
    }
}
