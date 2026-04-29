use crate::error::ReplError;
use hern_core::codegen::bundle::gen_lua_iife_bundle;
use hern_core::types::infer::TypeEnv;
use hern_core::workspace::{WorkspaceInputs, analyze_workspace};
use std::collections::HashMap;
use std::io::{self, Write};
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

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
    pub(crate) fn new() -> Result<Self> {
        let entry_path = std::env::current_dir()?.join(".hern_repl.hern");
        Ok(Self {
            defs: String::new(),
            entry_path,
        })
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
    let mut child = Command::new("luajit")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .or_else(|_| {
            Command::new("lua")
                .stdin(Stdio::piped())
                .stdout(Stdio::piped())
                .stderr(Stdio::piped())
                .spawn()
        })?;

    let mut stdin = child
        .stdin
        .take()
        .ok_or_else(|| io::Error::new(io::ErrorKind::BrokenPipe, "failed to open Lua stdin"))?;
    stdin.write_all(lua_code.as_bytes())?;
    drop(stdin);

    let output = child.wait_with_output()?;
    let mut text = String::new();
    text.push_str(&String::from_utf8_lossy(&output.stdout));
    if !output.status.success() {
        text.push_str(&String::from_utf8_lossy(&output.stderr));
        return Err(ReplError::Io(io::Error::other(text.trim().to_string())));
    }
    if !output.stderr.is_empty() {
        text.push_str(&String::from_utf8_lossy(&output.stderr));
    }
    Ok(text)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn type_hint_handles_plain_expression() {
        let session = ReplSession::new().expect("session should initialize");
        let source = append_source("", "let hern_repl_hint_value = 2 + 2;");
        let env = analyze_env(&source, &session.entry_path).expect("expression should typecheck");

        assert_eq!(session.type_hint("2 + 2").as_deref(), Some("f64"));
        assert!(env.get(TYPE_HINT_BINDING).is_some());
    }
}
