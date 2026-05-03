use crate::error::ReplError;
use hern_core::ast::{Program, SourceSpan, Stmt};
use hern_core::codegen::bundle::gen_lua_iife_bundle;
use hern_core::types::Ty;
use hern_core::types::infer::TypeEnv;
use hern_core::workspace::{WorkspaceInputs, analyze_workspace};
use mlua::{Function, Lua, MultiValue};
use std::cell::RefCell;
use std::collections::HashMap;
use std::fs;
use std::path::{Path, PathBuf};
use std::rc::Rc;

type Result<T> = std::result::Result<T, ReplError>;
const TYPE_HINT_BINDING: &str = "hern_repl_hint_value";

pub(crate) struct ReplSession {
    defs: String,
    entry_path: PathBuf,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct BindingInfo {
    pub(crate) name: String,
    pub(crate) ty: String,
}

impl ReplSession {
    pub(crate) fn new(path: Option<&Path>) -> Result<Self> {
        let (defs, entry_path) = match path {
            Some(path) => {
                let source = fs::read_to_string(path)?;
                let entry_path = path.canonicalize().unwrap_or_else(|_| path.to_path_buf());
                let (graph, _inference, entry) = analyze_source(&source, &entry_path)?;
                let defs = graph
                    .modules
                    .get(&entry)
                    .map(|program| source_without_top_level_exprs(&source, program))
                    .unwrap_or(source);
                (defs, entry_path)
            }
            None => (
                String::new(),
                std::env::current_dir()?.join(".hern_repl.hern"),
            ),
        };
        Ok(Self { defs, entry_path })
    }

    pub(crate) fn eval(&mut self, input: &str) -> Result<String> {
        let definition = looks_like_definition(input);
        let source = if definition {
            append_source(&self.defs, input)
        } else {
            append_source(&self.defs, &format!("print({input})"))
        };

        let output = compile_and_run(&source, &self.entry_path)?;
        if definition {
            self.defs = append_source(&self.defs, input);
        }
        Ok(output)
    }

    pub(crate) fn bindings(&self) -> Vec<BindingInfo> {
        let Ok(env) = analyze_env(&self.defs, &self.entry_path) else {
            return Vec::new();
        };
        let mut bindings: Vec<_> = env
            .0
            .into_iter()
            .filter(|(name, _)| !name.starts_with("__hern_") && !name.starts_with("_t_"))
            .map(|(name, info)| BindingInfo {
                name,
                ty: info.to_string(),
            })
            .collect();
        bindings.sort_by(|a, b| a.name.cmp(&b.name));
        bindings
    }

    pub(crate) fn member_bindings(&self, base: &str, prefix: &str) -> Vec<BindingInfo> {
        let Ok(env) = analyze_env(&self.defs, &self.entry_path) else {
            return Vec::new();
        };
        let Some(info) = env.get(base) else {
            return Vec::new();
        };
        let prefix = prefix.to_lowercase();
        let mut fields: Vec<_> = record_fields(&info.scheme.ty)
            .into_iter()
            .filter(|(name, _)| prefix.is_empty() || name.to_lowercase().starts_with(&prefix))
            .map(|(name, ty)| BindingInfo {
                name,
                ty: ty.to_string(),
            })
            .collect();
        fields.sort_by(|a, b| a.name.cmp(&b.name));
        fields
    }

    pub(crate) fn type_hint(&self, input: &str) -> Option<String> {
        let trimmed = input.trim();
        if trimmed.is_empty() || looks_like_definition(trimmed) {
            return None;
        }

        let source = append_source(&self.defs, &format!("let {TYPE_HINT_BINDING} = {trimmed};"));
        let env = analyze_env(&source, &self.entry_path).ok()?;
        env.get(TYPE_HINT_BINDING).map(ToString::to_string)
    }
}

fn append_source(base: &str, addition: &str) -> String {
    let mut out = String::with_capacity(base.len() + addition.len() + 2);
    out.push_str(base);
    if !out.is_empty() && !out.ends_with('\n') {
        out.push('\n');
    }
    out.push_str(addition.trim_end());
    out.push('\n');
    out
}

fn looks_like_definition(input: &str) -> bool {
    let first = input
        .lines()
        .map(str::trim_start)
        .find(|line| !line.is_empty() && !line.starts_with("//"))
        .unwrap_or("");
    matches!(
        first.split_whitespace().next(),
        Some("let" | "fn" | "type" | "trait" | "impl" | "extern")
    )
}

fn record_fields(ty: &Ty) -> Vec<(String, Ty)> {
    match ty {
        Ty::Record(row) => row.fields.clone(),
        Ty::Qualified(_, inner) => record_fields(inner),
        _ => Vec::new(),
    }
}

fn source_without_top_level_exprs(source: &str, program: &Program) -> String {
    let mut out = String::new();
    for stmt in &program.stmts {
        if matches!(stmt, Stmt::Expr(_)) {
            continue;
        }
        if let Some(snippet) = source_slice(source, stmt.span()) {
            if !out.is_empty() && !out.ends_with('\n') {
                out.push('\n');
            }
            out.push_str(snippet.trim_end());
            out.push('\n');
        }
    }
    out
}

fn source_slice(source: &str, span: SourceSpan) -> Option<&str> {
    if span.start_line == 0 || span.end_line == 0 {
        return None;
    }

    let mut line_start = 0usize;
    let mut start = None;
    let mut end = None;
    for (line_idx, line) in source.split_inclusive('\n').enumerate() {
        let line_no = line_idx + 1;
        if line_no == span.start_line {
            start = Some(line_start + span.start_col.saturating_sub(1));
        }
        if line_no == span.end_line {
            end = Some(line_start + span.end_col.saturating_sub(1).min(line.len()));
            break;
        }
        line_start += line.len();
    }

    let start = start?;
    let end = end?;
    source.get(start..end)
}

fn compile_and_run(source: &str, entry_path: &Path) -> Result<String> {
    let (graph, inference, entry) = analyze_source(source, entry_path)?;
    let lua_code = gen_lua_iife_bundle(&graph, &inference.module_envs, &entry);
    run_lua(&lua_code)
}

fn analyze_env(source: &str, entry_path: &Path) -> Result<TypeEnv> {
    let (_graph, inference, entry) = analyze_source(source, entry_path)?;
    inference
        .env_for_module(&entry)
        .cloned()
        .ok_or(ReplError::MissingAnalysis(
            "workspace analysis did not return an entry type environment",
        ))
}

fn analyze_source(
    source: &str,
    entry_path: &Path,
) -> Result<(
    hern_core::module::ModuleGraph,
    hern_core::module::GraphInference,
    String,
)> {
    let mut overlays = HashMap::new();
    overlays.insert(entry_path.to_path_buf(), source.to_string());
    let analysis = analyze_workspace(WorkspaceInputs {
        entry: entry_path.to_path_buf(),
        overlays,
        prelude: None,
    });
    if !analysis.diagnostics.is_empty() {
        return Err(ReplError::Diagnostics(analysis.diagnostics));
    }
    let graph = analysis.graph.ok_or(ReplError::MissingAnalysis(
        "workspace analysis did not return a graph",
    ))?;
    let inference = analysis.inference.ok_or(ReplError::MissingAnalysis(
        "workspace analysis did not return inference results",
    ))?;
    let entry = analysis.entry.ok_or(ReplError::MissingAnalysis(
        "workspace analysis did not return an entry module",
    ))?;
    Ok((graph, inference, entry))
}

fn run_lua(lua_code: &str) -> Result<String> {
    let lua = Lua::new();
    let buf = Rc::new(RefCell::new(String::new()));

    let tostring: Function = lua.globals().get("tostring")?;
    let buf_clone = Rc::clone(&buf);
    let print_fn = lua.create_function(move |_lua, args: MultiValue| {
        let mut line = String::new();
        for (i, v) in args.iter().enumerate() {
            if i > 0 {
                line.push('\t');
            }
            let s: String = tostring.call(v.clone())?;
            line.push_str(&s);
        }
        line.push('\n');
        buf_clone.borrow_mut().push_str(&line);
        Ok(())
    })?;
    lua.globals().set("print", print_fn)?;

    lua.load(lua_code).exec()?;

    Ok(buf.borrow().clone())
}

pub(crate) fn exec_lua_passthrough(lua_code: &str) -> Result<()> {
    Lua::new().load(lua_code).exec()?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::{SystemTime, UNIX_EPOCH};

    #[test]
    fn type_hint_handles_plain_expression() {
        let session = ReplSession::new(None).expect("session should initialize");
        let source = append_source("", "let hern_repl_hint_value = 2 + 2;");
        let env = analyze_env(&source, &session.entry_path).expect("expression should typecheck");

        assert_eq!(session.type_hint("2 + 2").as_deref(), Some("f64"));
        assert!(env.get(TYPE_HINT_BINDING).is_some());
    }

    #[test]
    fn new_loads_initial_file_source() {
        let path = std::env::temp_dir().join(format!(
            "hern-repl-load-{}-{}.hern",
            std::process::id(),
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .expect("system time should be after epoch")
                .as_nanos()
        ));
        fs::write(&path, "let loaded_value = 41;\n").expect("fixture should be written");

        let session = ReplSession::new(Some(&path)).expect("session should load source");

        assert_eq!(
            session.type_hint("loaded_value + 1").as_deref(),
            Some("f64")
        );
        assert!(
            session
                .bindings()
                .iter()
                .any(|binding| binding.name == "loaded_value")
        );
        let _ = fs::remove_file(path);
    }

    #[test]
    fn loaded_file_drops_top_level_expressions_from_repl_context() {
        let source = "let loaded_value = 41;\nloaded_value\n";
        let path = std::env::temp_dir().join(format!(
            "hern-repl-strip-{}-{}.hern",
            std::process::id(),
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .expect("system time should be after epoch")
                .as_nanos()
        ));
        fs::write(&path, source).expect("fixture should be written");
        let (graph, _inference, entry) =
            analyze_source(source, &path).expect("fixture should analyze");
        let program = graph
            .modules
            .get(&entry)
            .expect("entry module should exist");

        assert_eq!(
            source_without_top_level_exprs(source, program),
            "let loaded_value = 41;\n"
        );
        let _ = fs::remove_file(path);
    }

    #[test]
    fn eval_unbound_variable_returns_diagnostic() {
        let mut session = ReplSession::new(None).expect("session should initialize");
        let result = session.eval("unbound_var_123");
        match result {
            Err(ReplError::Diagnostics(diagnostics)) => {
                assert!(!diagnostics.is_empty());
                assert!(diagnostics[0].message.contains("unbound"));
            }
            other => panic!("expected diagnostic error, got {:?}", other),
        }
    }

    #[test]
    fn member_bindings_returns_record_fields() {
        let path = std::env::temp_dir().join(format!(
            "hern-repl-members-{}-{}.hern",
            std::process::id(),
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .expect("system time should be after epoch")
                .as_nanos()
        ));
        fs::write(&path, "let math = #{ cos: 1, sin: 2 };\n").expect("fixture should be written");
        let session = ReplSession::new(Some(&path)).expect("session should load source");

        let fields = session.member_bindings("math", "s");

        assert_eq!(fields.first().map(|field| field.name.as_str()), Some("sin"));
        let _ = fs::remove_file(path);
    }
}
