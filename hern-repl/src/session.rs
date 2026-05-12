use crate::error::ReplError;
use hern_core::ast::{Expr, ExprKind, Program, SourceSpan, Stmt};
use hern_core::codegen::bundle::gen_lua_iife_bundle;
use hern_core::module::ModuleEnv;
use hern_core::pipeline::parse_source;
use hern_core::types::infer::TypeEnv;
use hern_core::types::{ParamCapability, Ty, inherent_impl_target_keys_from_ty};
use hern_core::workspace::{WorkspaceInputs, analyze_workspace};
use mlua::{Function, Lua, MultiValue};
use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::fs;
use std::path::{Path, PathBuf};
use std::rc::Rc;

type Result<T> = std::result::Result<T, ReplError>;
const TYPE_HINT_BINDING: &str = "hern_repl_hint_value";

pub(crate) struct ReplSession {
    defs: String,
    entry_path: PathBuf,
    analysis_cache: RefCell<Option<SessionAnalysis>>,
}

#[derive(Clone)]
struct SessionAnalysis {
    source: String,
    env: TypeEnv,
    module_env: ModuleEnv,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ReplInputKind {
    Definition,
    Statement,
    Expression,
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
        Ok(Self {
            defs,
            entry_path,
            analysis_cache: RefCell::new(None),
        })
    }

    pub(crate) fn eval(&mut self, input: &str) -> Result<String> {
        let kind = classify_input(input);
        let source = if matches!(kind, ReplInputKind::Expression) {
            append_source(&self.defs, &format!("print({input})"))
        } else {
            append_source(&self.defs, input)
        };

        let (graph, inference, entry) = analyze_source(&source, &self.entry_path)?;
        let lua_code = gen_lua_iife_bundle(&graph, &inference.module_envs, &entry);
        let output = run_lua(&lua_code)?;
        if !matches!(kind, ReplInputKind::Expression) {
            if let Some(program) = graph.modules.get(&entry) {
                self.defs = source_without_transient_repl_exprs(&source, program);
            } else {
                self.defs = source;
            }
            self.analysis_cache.borrow_mut().take();
        }
        Ok(output)
    }

    pub(crate) fn bindings(&self) -> Vec<BindingInfo> {
        let Ok(analysis) = self.analysis() else {
            return Vec::new();
        };
        let mut bindings: Vec<_> = analysis
            .env
            .0
            .into_iter()
            .filter(|(name, _)| !is_internal_binding_name(name))
            .map(|(name, info)| BindingInfo {
                name,
                ty: info.to_string(),
            })
            .collect();
        bindings.sort_by(|a, b| a.name.cmp(&b.name));
        bindings
    }

    pub(crate) fn member_bindings(&self, base: &str, prefix: &str) -> Vec<BindingInfo> {
        let Ok(analysis) = self.analysis() else {
            return Vec::new();
        };
        let Some(info) = analysis.env.get(base) else {
            return Vec::new();
        };
        let prefix = prefix.to_lowercase();
        let mut seen = HashSet::new();
        let mut bindings: Vec<_> = record_fields(&info.scheme.ty)
            .into_iter()
            .filter(|(name, _)| binding_matches_prefix(name, &prefix))
            .map(|(name, ty)| {
                seen.insert(name.clone());
                BindingInfo {
                    name,
                    ty: ty.to_string(),
                }
            })
            .collect();

        for target in inherent_impl_target_keys_from_ty(&info.scheme.ty) {
            for (_, methods) in analysis
                .module_env
                .all_inherent_methods()
                .filter(|(method_target, _)| *method_target == target)
            {
                for (name, method) in methods {
                    if is_internal_binding_name(name)
                        || !method.has_receiver
                        || (!info.is_place_mutable()
                            && scheme_param_capability(&method.scheme, 0).is_mut_place())
                        || !binding_matches_prefix(name, &prefix)
                        || !seen.insert(name.clone())
                    {
                        continue;
                    }
                    bindings.push(BindingInfo {
                        name: name.clone(),
                        ty: method.scheme.to_string(),
                    });
                }
            }
        }

        bindings.sort_by(|a, b| a.name.cmp(&b.name));
        bindings
    }

    fn analysis(&self) -> Result<SessionAnalysis> {
        if let Some(cached) = self.analysis_cache.borrow().as_ref()
            && cached.source == self.defs
        {
            return Ok(cached.clone());
        }

        let (_graph, inference, entry) = analyze_source(&self.defs, &self.entry_path)?;
        let env = inference
            .env_for_module(&entry)
            .cloned()
            .ok_or(ReplError::MissingAnalysis(
                "workspace analysis did not return an entry type environment",
            ))?;
        let module_env =
            inference
                .module_env_for_module(&entry)
                .cloned()
                .ok_or(ReplError::MissingAnalysis(
                    "workspace analysis did not return an entry module environment",
                ))?;
        let analysis = SessionAnalysis {
            source: self.defs.clone(),
            env,
            module_env,
        };
        *self.analysis_cache.borrow_mut() = Some(analysis.clone());
        Ok(analysis)
    }

    pub(crate) fn type_hint(&self, input: &str) -> Option<String> {
        let trimmed = input.trim();
        if trimmed.is_empty() || !matches!(classify_input(trimmed), ReplInputKind::Expression) {
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

fn classify_input(input: &str) -> ReplInputKind {
    let Ok(program) = parse_source(input) else {
        return classify_input_lexically(input);
    };
    if program
        .stmts
        .iter()
        .any(|stmt| !matches!(stmt, Stmt::Expr(_)))
    {
        ReplInputKind::Definition
    } else if program.stmts.iter().any(|stmt| {
        matches!(
            stmt,
            Stmt::Expr(expr) if is_persistent_repl_expr(expr)
        )
    }) {
        ReplInputKind::Statement
    } else {
        ReplInputKind::Expression
    }
}

fn classify_input_lexically(input: &str) -> ReplInputKind {
    let first = first_code_line(input);
    if matches!(
        first.split_whitespace().next(),
        Some("let" | "fn" | "type" | "trait" | "impl" | "extern")
    ) {
        ReplInputKind::Definition
    } else {
        ReplInputKind::Expression
    }
}

fn first_code_line(input: &str) -> &str {
    input
        .lines()
        .map(str::trim_start)
        .find(|line| !line.is_empty() && !line.starts_with("//") && !line.starts_with("#!"))
        .unwrap_or("")
}

fn is_internal_binding_name(name: &str) -> bool {
    name.starts_with("__") || name.starts_with("_t_")
}

fn binding_matches_prefix(name: &str, prefix: &str) -> bool {
    prefix.is_empty() || name.to_lowercase().starts_with(prefix)
}

fn scheme_param_capability(scheme: &hern_core::types::Scheme, idx: usize) -> ParamCapability {
    match &scheme.ty {
        Ty::Func(params, _) => params
            .get(idx)
            .map(|param| param.capability)
            .unwrap_or(ParamCapability::Value),
        _ => ParamCapability::Value,
    }
}

fn record_fields(ty: &Ty) -> Vec<(String, Ty)> {
    match ty {
        Ty::Record(row) => row.fields.clone(),
        Ty::Qualified(_, inner) => record_fields(inner),
        _ => Vec::new(),
    }
}

fn source_without_top_level_exprs(source: &str, program: &Program) -> String {
    let mut out = leading_file_directives(source);
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

fn source_without_transient_repl_exprs(source: &str, program: &Program) -> String {
    let mut out = leading_file_directives(source);
    for stmt in &program.stmts {
        if matches!(stmt, Stmt::Expr(expr) if !is_persistent_repl_expr(expr)) {
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

fn is_persistent_repl_expr(expr: &Expr) -> bool {
    matches!(expr.kind, ExprKind::Assign { .. })
}

fn leading_file_directives(source: &str) -> String {
    let mut out = String::new();
    for line in source.split_inclusive('\n') {
        let trimmed = line.trim_start();
        if trimmed.is_empty() || trimmed.starts_with("//") || trimmed.starts_with("#!") {
            out.push_str(line);
            continue;
        }
        break;
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

        assert_eq!(session.type_hint("2 + 2").as_deref(), Some("int"));
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
            Some("int")
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
    fn loaded_file_preserves_leading_inner_attrs() {
        let source = "#![no_implicit_prelude]\nlet loaded_value = 41;\nloaded_value\n";
        let path = std::env::temp_dir().join(format!(
            "hern-repl-attrs-{}-{}.hern",
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
            "#![no_implicit_prelude]\nlet loaded_value = 41;\n"
        );
        let _ = fs::remove_file(path);
    }

    #[test]
    fn eval_definition_strips_trailing_top_level_expressions() {
        let mut session = ReplSession::new(None).expect("session should initialize");

        assert_eq!(
            session
                .eval("let x = 1;\nprint(x)")
                .expect("definition should evaluate"),
            "1\n"
        );
        assert_eq!(session.eval("x").expect("x should remain bound"), "1\n");
    }

    #[test]
    fn eval_assignment_persists_in_replay_context() {
        let mut session = ReplSession::new(None).expect("session should initialize");

        assert_eq!(session.eval("let mut x = 1;").expect("let should work"), "");
        assert_eq!(
            session.eval("x = x + 1").expect("assignment should work"),
            ""
        );
        assert_eq!(session.eval("x").expect("x should be updated"), "2\n");
        assert_eq!(
            session.eval("x = x + 1").expect("assignment should work"),
            ""
        );
        assert_eq!(session.eval("x").expect("x should be updated again"), "3\n");
    }

    #[test]
    fn bindings_hide_internal_names() {
        let session = ReplSession::new(None).expect("session should initialize");

        assert!(
            session
                .bindings()
                .iter()
                .all(|binding| !is_internal_binding_name(&binding.name))
        );
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

    #[test]
    fn member_bindings_returns_inherent_receiver_methods() {
        let path = std::env::temp_dir().join(format!(
            "hern-repl-methods-{}-{}.hern",
            std::process::id(),
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .expect("system time should be after epoch")
                .as_nanos()
        ));
        fs::write(&path, "let xs = [1.0, 2.0, 3.0];\n").expect("fixture should be written");
        let session = ReplSession::new(Some(&path)).expect("session should load source");

        let methods = session.member_bindings("xs", "s");

        assert!(methods.iter().any(|method| method.name == "sum"));
        let _ = fs::remove_file(path);
    }
}
