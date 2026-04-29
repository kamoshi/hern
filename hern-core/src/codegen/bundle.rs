use crate::ast::Stmt;
use crate::codegen::lua::{ImportMode, LuaCodegen};
use crate::module::{ModuleEnv, ModuleGraph, collect_imports_in_program};
use std::collections::HashMap;

const PRELUDE_MODULE: &str = "hern_prelude";

pub fn gen_lua_bundle(
    graph: &ModuleGraph,
    module_envs: &HashMap<String, ModuleEnv>,
    entry: &str,
) -> String {
    let mut out = String::new();
    let prelude_stmts = prelude_stmts(graph);
    let mut prelude_codegen = LuaCodegen::new();
    out.push_str(&format!(
        "package.preload[{}] = function()\n",
        lua_quote(PRELUDE_MODULE)
    ));
    out.push_str(&prelude_codegen.gen_prelude_module(prelude_stmts));
    out.push_str("\nend\n");

    for name in graph.order.iter().filter(|name| *name != entry) {
        let program = graph.module(name).expect("loaded module missing");
        let mut codegen = LuaCodegen::new();
        out.push_str(&format!(
            "package.preload[{}] = function()\n",
            lua_quote(name)
        ));
        out.push_str(&format!(
            "local __prelude = require({})\n",
            lua_quote(PRELUDE_MODULE)
        ));
        out.push_str(&LuaCodegen::gen_prelude_aliases(prelude_stmts));
        out.push_str(&import_dict_bindings(
            graph,
            module_envs,
            name,
            ImportMode::Require,
        ));
        out.push_str(&codegen.gen_module_with_prelude_and_dicts(
            &graph.prelude,
            program,
            exported_dict_names(module_envs, name),
        ));
        out.push_str("\nend\n");
    }
    let mut codegen = LuaCodegen::new();
    let entry_program = graph.module(entry).expect("entry module missing");
    out.push_str(&format!(
        "local __prelude = require({})\n",
        lua_quote(PRELUDE_MODULE)
    ));
    out.push_str(&LuaCodegen::gen_prelude_aliases(prelude_stmts));
    out.push_str(&import_dict_bindings(
        graph,
        module_envs,
        entry,
        ImportMode::Require,
    ));
    out.push_str(&codegen.gen_program_with_prelude(&graph.prelude, entry_program));
    out
}

pub fn gen_lua_iife_bundle(
    graph: &ModuleGraph,
    module_envs: &HashMap<String, ModuleEnv>,
    entry: &str,
) -> String {
    let mut out = String::new();
    let prelude_stmts = prelude_stmts(graph);
    let mut prelude_codegen = LuaCodegen::new().with_import_mode(ImportMode::Bundle);
    out.push_str("local __prelude = (function()\n");
    out.push_str(&prelude_codegen.gen_prelude_module(prelude_stmts));
    out.push_str("end)()\n");

    for name in graph.order.iter().filter(|name| *name != entry) {
        let program = graph.module(name).expect("loaded module missing");
        let mut codegen = LuaCodegen::new().with_import_mode(ImportMode::Bundle);
        out.push_str(&format!(
            "local {} = (function(__prelude)\n",
            bundle_module_var(name)
        ));
        out.push_str(&LuaCodegen::gen_prelude_aliases(prelude_stmts));
        out.push_str(&import_dict_bindings(
            graph,
            module_envs,
            name,
            ImportMode::Bundle,
        ));
        out.push_str(&codegen.gen_module_with_prelude_and_dicts(
            &graph.prelude,
            program,
            exported_dict_names(module_envs, name),
        ));
        out.push_str("end)(__prelude)\n");
    }
    let mut codegen = LuaCodegen::new().with_import_mode(ImportMode::Bundle);
    let entry_program = graph.module(entry).expect("entry module missing");
    out.push_str(&LuaCodegen::gen_prelude_aliases(prelude_stmts));
    out.push_str(&import_dict_bindings(
        graph,
        module_envs,
        entry,
        ImportMode::Bundle,
    ));
    out.push_str(&codegen.gen_program_with_prelude(&graph.prelude, entry_program));
    out
}

fn lua_quote(s: &str) -> String {
    let escaped = s
        .replace('\\', "\\\\")
        .replace('"', "\\\"")
        .replace('\n', "\\n")
        .replace('\r', "\\r")
        .replace('\t', "\\t");
    format!("\"{}\"", escaped)
}

fn prelude_stmts(graph: &ModuleGraph) -> &[Stmt] {
    &graph.prelude.stmts
}

fn bundle_module_var(name: &str) -> String {
    format!("__mod_{}", name)
}

fn exported_dict_names(module_envs: &HashMap<String, ModuleEnv>, name: &str) -> Vec<String> {
    module_envs
        .get(name)
        .map(ModuleEnv::exported_dict_names)
        .unwrap_or_default()
}

fn import_dict_bindings(
    graph: &ModuleGraph,
    module_envs: &HashMap<String, ModuleEnv>,
    name: &str,
    mode: ImportMode,
) -> String {
    let program = graph.module(name).expect("loaded module missing");
    let imports = collect_imports_in_program(program);
    let mut bindings = HashMap::<String, String>::new();
    for import in imports {
        let Some(env) = module_envs.get(&import) else {
            continue;
        };
        let module_ref = match mode {
            ImportMode::Require => format!("require({})", lua_quote(&import)),
            ImportMode::Bundle => bundle_module_var(&import),
        };
        for dict_name in env.exported_dict_names() {
            bindings
                .entry(dict_name.clone())
                .or_insert_with(|| format!("{}.__hern_dicts.{}", module_ref, dict_name));
        }
    }
    let mut names: Vec<_> = bindings.into_iter().collect();
    names.sort_by(|(a, _), (b, _)| a.cmp(b));
    let mut out = String::new();
    for (dict_name, source) in names {
        out.push_str(&format!("local {} = {}\n", dict_name, source));
    }
    out
}
