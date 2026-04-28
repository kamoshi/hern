use crate::analysis::{CompilerDiagnostic, analyze_prelude};
use crate::ast::Program;
use crate::module::{GraphInference, ModuleGraph, infer_graph_collecting};
use std::collections::HashMap;
use std::path::PathBuf;

pub struct WorkspaceInputs {
    pub entry: PathBuf,
    pub overlays: HashMap<PathBuf, String>,
    pub prelude: Option<Program>,
}

pub struct WorkspaceAnalysis {
    pub graph: Option<ModuleGraph>,
    pub entry: Option<String>,
    pub inference: Option<GraphInference>,
    pub diagnostics: Vec<CompilerDiagnostic>,
}

pub fn analyze_workspace(inputs: WorkspaceInputs) -> WorkspaceAnalysis {
    let prelude = match inputs.prelude {
        Some(prelude) => prelude,
        None => match analyze_prelude() {
            Ok(prelude) => prelude.program,
            Err(diagnostic) => return diagnostics_only(vec![diagnostic]),
        },
    };

    let loaded = ModuleGraph::load_entry_with_prelude_and_overlays_recovering(
        &inputs.entry,
        prelude,
        inputs.overlays,
    );
    if !loaded.diagnostics.is_empty() {
        let (graph, entry) = loaded
            .value
            .map(|loaded| (Some(loaded.graph), Some(loaded.entry)))
            .unwrap_or((None, None));
        return WorkspaceAnalysis {
            graph,
            entry,
            inference: None,
            diagnostics: loaded.diagnostics,
        };
    }

    let Some(loaded) = loaded.value else {
        return WorkspaceAnalysis {
            graph: None,
            entry: None,
            inference: None,
            diagnostics: Vec::new(),
        };
    };

    let mut graph = loaded.graph;
    let inference = infer_graph_collecting(&mut graph);
    if inference.diagnostics.is_empty() {
        WorkspaceAnalysis {
            graph: Some(graph),
            entry: Some(loaded.entry),
            inference: inference.value,
            diagnostics: Vec::new(),
        }
    } else {
        WorkspaceAnalysis {
            graph: Some(graph),
            entry: Some(loaded.entry),
            inference: inference.value,
            diagnostics: inference.diagnostics,
        }
    }
}

fn diagnostics_only(diagnostics: Vec<CompilerDiagnostic>) -> WorkspaceAnalysis {
    WorkspaceAnalysis {
        graph: None,
        entry: None,
        inference: None,
        diagnostics,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::analysis::DiagnosticSource;
    use std::fs;
    use std::time::{SystemTime, UNIX_EPOCH};

    fn temp_dir(name: &str) -> PathBuf {
        let path = std::env::temp_dir().join(format!(
            "hern-workspace-{name}-{}-{}",
            std::process::id(),
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .expect("system time should be after epoch")
                .as_nanos()
        ));
        fs::create_dir_all(&path).expect("temp test directory should be created");
        path
    }

    #[test]
    fn workspace_analysis_returns_successful_graph_and_inference() {
        let test_dir = temp_dir("success");
        let entry = test_dir.join("main.hern");
        fs::write(&entry, "let value = 1;\nvalue\n").expect("entry should be written");

        let analysis = analyze_workspace(WorkspaceInputs {
            entry,
            overlays: HashMap::new(),
            prelude: None,
        });

        assert!(analysis.diagnostics.is_empty());
        assert!(analysis.graph.is_some());
        assert!(analysis.inference.is_some());
    }

    #[test]
    fn workspace_analysis_collects_imported_parse_diagnostics() {
        let test_dir = temp_dir("imported-parse");
        let entry = test_dir.join("main.hern");
        let dep = test_dir.join("dep.hern");
        fs::write(&entry, "let dep = import \"dep\";\n").expect("entry should be written");
        fs::write(&dep, "let a = ;\nlet b = ;\n").expect("dep should be written");
        let dep = fs::canonicalize(dep).expect("dep path should canonicalize");

        let analysis = analyze_workspace(WorkspaceInputs {
            entry,
            overlays: HashMap::new(),
            prelude: None,
        });

        assert!(analysis.graph.is_some());
        assert!(analysis.inference.is_none());
        assert_eq!(analysis.diagnostics.len(), 2);
        assert!(
            analysis.diagnostics.iter().all(|diagnostic| {
                diagnostic.source == Some(DiagnosticSource::Path(dep.clone()))
            })
        );
    }

    #[test]
    fn workspace_analysis_returns_graph_with_type_diagnostic() {
        let test_dir = temp_dir("type-error");
        let entry = test_dir.join("main.hern");
        fs::write(&entry, "let value: bool = 1;\n").expect("entry should be written");

        let analysis = analyze_workspace(WorkspaceInputs {
            entry,
            overlays: HashMap::new(),
            prelude: None,
        });

        assert!(analysis.graph.is_some());
        assert!(analysis.inference.is_some());
        assert_eq!(analysis.diagnostics.len(), 1);
        assert!(analysis.diagnostics[0].message.contains("type error"));
    }

    #[test]
    fn workspace_analysis_collects_independent_module_type_diagnostics() {
        let test_dir = temp_dir("independent-type-errors");
        let entry = test_dir.join("main.hern");
        let dep_a = test_dir.join("a.hern");
        let dep_b = test_dir.join("b.hern");
        fs::write(
            &entry,
            "let a = import \"a\";\nlet b = import \"b\";\n#{ a: a, b: b }\n",
        )
        .expect("entry should be written");
        fs::write(&dep_a, "let value: bool = 1;\n").expect("dep a should be written");
        fs::write(&dep_b, "let value: bool = 2;\n").expect("dep b should be written");

        let analysis = analyze_workspace(WorkspaceInputs {
            entry,
            overlays: HashMap::new(),
            prelude: None,
        });

        assert!(analysis.graph.is_some());
        assert!(analysis.inference.is_some());
        assert_eq!(analysis.diagnostics.len(), 2);
        assert!(
            analysis
                .diagnostics
                .iter()
                .all(|diagnostic| diagnostic.message.contains("type error"))
        );
    }

    #[test]
    fn workspace_analysis_collects_multiple_entry_type_diagnostics() {
        let test_dir = temp_dir("entry-type-errors");
        let entry = test_dir.join("main.hern");
        fs::write(&entry, "let a: bool = 1;\nlet b: bool = 2;\n").expect("entry should be written");

        let analysis = analyze_workspace(WorkspaceInputs {
            entry,
            overlays: HashMap::new(),
            prelude: None,
        });

        assert!(analysis.graph.is_some());
        assert!(analysis.inference.is_some());
        assert_eq!(analysis.diagnostics.len(), 2);
        assert!(
            analysis
                .diagnostics
                .iter()
                .all(|diagnostic| diagnostic.message.contains("type error"))
        );
    }

    #[test]
    fn workspace_analysis_skips_dependent_entry_type_cascades() {
        let test_dir = temp_dir("entry-type-cascade");
        let entry = test_dir.join("main.hern");
        fs::write(
            &entry,
            "let bad: bool = 1;\nlet dependent = bad;\nlet other_bad: bool = 2;\n",
        )
        .expect("entry should be written");

        let analysis = analyze_workspace(WorkspaceInputs {
            entry,
            overlays: HashMap::new(),
            prelude: None,
        });

        assert!(analysis.graph.is_some());
        assert!(analysis.inference.is_some());
        assert_eq!(analysis.diagnostics.len(), 2);
        assert_eq!(
            analysis
                .diagnostics
                .iter()
                .map(|diagnostic| diagnostic.span.expect("type error span").start_line)
                .collect::<Vec<_>>(),
            vec![1, 3]
        );
    }
}
