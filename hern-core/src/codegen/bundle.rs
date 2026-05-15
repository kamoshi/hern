use crate::ast::Stmt;
use crate::codegen::lua::{ImportMode, LuaCodegen, TestEmitMode, test_function_names};
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
        out.push_str(&LuaCodegen::gen_prelude_env_setup());
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
    out.push_str(&LuaCodegen::gen_prelude_env_setup());
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

pub fn gen_lua_iife_test_bundle(
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
        let mut codegen = LuaCodegen::new()
            .with_import_mode(ImportMode::Bundle)
            .with_test_emit_mode(TestEmitMode::Include);
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

    let mut codegen = LuaCodegen::new()
        .with_import_mode(ImportMode::Bundle)
        .with_test_emit_mode(TestEmitMode::Include);
    let entry_program = graph.module(entry).expect("entry module missing");
    out.push_str(&LuaCodegen::gen_prelude_aliases(prelude_stmts));
    out.push_str(&import_dict_bindings(
        graph,
        module_envs,
        entry,
        ImportMode::Bundle,
    ));
    out.push_str(&codegen.gen_program_with_prelude(&graph.prelude, entry_program));
    out.push_str(&gen_test_harness(graph, entry, entry_program));
    out
}

fn gen_test_harness(
    graph: &ModuleGraph,
    entry: &str,
    entry_program: &crate::ast::Program,
) -> String {
    let mut out = String::new();
    out.push_str("local __hern_tests = {}\n");
    out.push_str("local function __hern_add_tests(prefix, tests)\n");
    out.push_str("  for _, test in ipairs(tests or {}) do\n");
    out.push_str(
        "    table.insert(__hern_tests, { name = prefix .. \"::\" .. test.name, fn = test.fn })\n",
    );
    out.push_str("  end\n");
    out.push_str("end\n");
    for name in graph.order.iter().filter(|name| *name != entry) {
        out.push_str(&format!(
            "__hern_add_tests({}, {}.__hern_tests)\n",
            lua_quote(&test_module_label(graph, name)),
            bundle_module_var(name)
        ));
    }
    out.push_str(&format!(
        "__hern_add_tests({}, {{\n",
        lua_quote(&test_module_label(graph, entry))
    ));
    for name in test_function_names(entry_program) {
        out.push_str(&format!(
            "  {{ name = {}, fn = {} }},\n",
            lua_quote(&name),
            name
        ));
    }
    out.push_str("})\n");
    out.push_str("local __hern_passed = 0\n");
    out.push_str("local __hern_failed = 0\n");
    out.push_str("for _, test in ipairs(__hern_tests) do\n");
    out.push_str("  local ok, err = pcall(test.fn)\n");
    out.push_str("  if ok then\n");
    out.push_str("    __hern_passed = __hern_passed + 1\n");
    out.push_str("    print(\"ok \" .. test.name)\n");
    out.push_str("  else\n");
    out.push_str("    __hern_failed = __hern_failed + 1\n");
    out.push_str("    print(\"FAILED \" .. test.name .. \": \" .. tostring(err))\n");
    out.push_str("  end\n");
    out.push_str("end\n");
    out.push_str("print(tostring(__hern_passed) .. \" passed; \" .. tostring(__hern_failed) .. \" failed\")\n");
    out.push_str("if __hern_failed ~= 0 then error(\"test failure\") end\n");
    out
}

fn test_module_label(graph: &ModuleGraph, name: &str) -> String {
    let Some(path) = graph.module_path(name) else {
        return name.to_string();
    };
    let Some(stem) = path.file_stem().and_then(|stem| stem.to_str()) else {
        return name.to_string();
    };
    let stem_collisions = graph
        .paths
        .values()
        .filter_map(|path| path.file_stem().and_then(|stem| stem.to_str()))
        .filter(|other| *other == stem)
        .count();
    if stem_collisions <= 1 {
        return stem.to_string();
    }
    path.parent()
        .and_then(|parent| parent.file_name())
        .and_then(|parent| parent.to_str())
        .map(|parent| format!("{}::{}", parent, stem))
        .unwrap_or_else(|| name.to_string())
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
