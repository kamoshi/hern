use clap::{Parser as ClapParser, Subcommand};
use hern_core::analysis::CompilerDiagnostic;
use hern_core::ast::Stmt;
use hern_core::codegen::lua::{ImportMode, LuaCodegen};
use hern_core::module::{
    ModuleEnv, ModuleGraph, collect_imports_in_program, parse_file_recovering,
};
use hern_core::workspace::{WorkspaceInputs, analyze_workspace};
use std::collections::HashMap;
use std::fmt;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

#[derive(ClapParser)]
#[command(name = "hern")]
#[command(about = "Hern language CLI", long_about = None)]
struct Cli {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum Commands {
    /// Parse a file and print the AST
    Parse {
        /// Path to the file to parse
        path: PathBuf,
    },
    /// Parse and typecheck a file
    Typecheck {
        /// Path to the file to typecheck
        path: PathBuf,
        /// Dump all resolved types
        #[arg(long)]
        dump: bool,
    },
    /// Compile Hern to Lua
    Lua {
        /// Path to the file to compile
        path: PathBuf,
    },
    /// Run Hern via Lua
    Run {
        /// Path to the file to run
        path: PathBuf,
    },
    /// Bundle Hern and all imports into a single Lua file
    Bundle {
        /// Path to the file to bundle
        path: PathBuf,
    },
    /// Start the Hern language server (LSP)
    Lsp,
}

fn main() {
    if let Err(err) = run_cli() {
        eprintln!("{}", err);
        std::process::exit(1);
    }
}

#[derive(Debug)]
enum CliError {
    Single(CompilerDiagnostic),
    Diagnostics(Vec<CompilerDiagnostic>),
}

impl From<CompilerDiagnostic> for CliError {
    fn from(diagnostic: CompilerDiagnostic) -> Self {
        Self::Single(diagnostic)
    }
}

impl From<Vec<CompilerDiagnostic>> for CliError {
    fn from(diagnostics: Vec<CompilerDiagnostic>) -> Self {
        Self::Diagnostics(diagnostics)
    }
}

impl fmt::Display for CliError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CliError::Single(diagnostic) => write!(f, "{}", diagnostic),
            CliError::Diagnostics(diagnostics) => {
                for (idx, diagnostic) in diagnostics.iter().enumerate() {
                    if idx > 0 {
                        writeln!(f)?;
                    }
                    write!(f, "{}", diagnostic)?;
                }
                Ok(())
            }
        }
    }
}

impl std::error::Error for CliError {}

fn run_cli() -> Result<(), CliError> {
    let cli = Cli::parse();

    match cli.command {
        Commands::Parse { path } => {
            let program = parse_file_for_cli(&path)?;
            println!("{:#?}", program);
        }
        Commands::Typecheck { path, dump } => {
            let (_graph, inference, entry) = analyze_workspace_for_cli(path)?;
            if dump {
                println!("Resolved types:");
                if let Some(env) = inference.env_for_module(&entry) {
                    print!("{}", env);
                }
            } else {
                println!("Typecheck successful!");
            }
        }
        Commands::Lua { path } => {
            let (graph, inference, entry) = analyze_workspace_for_cli(path)?;
            println!("{}", gen_lua_bundle(&graph, &inference.module_envs, &entry));
        }
        Commands::Run { path } => {
            let (graph, inference, entry) = analyze_workspace_for_cli(path)?;
            let lua_code = gen_lua_iife_bundle(&graph, &inference.module_envs, &entry);

            let mut child = Command::new("luajit")
                .stdin(Stdio::piped())
                .spawn()
                .or_else(|_| Command::new("lua").stdin(Stdio::piped()).spawn())
                .expect("Failed to execute luajit or lua. Is it installed?");

            let mut stdin = child.stdin.take().expect("Failed to open stdin");
            stdin
                .write_all(lua_code.as_bytes())
                .expect("Failed to write to stdin");
            drop(stdin);

            let status = child.wait().expect("Failed to wait on child");
            if !status.success() {
                std::process::exit(status.code().unwrap_or(1));
            }
        }
        Commands::Bundle { path } => {
            let (graph, inference, entry) = analyze_workspace_for_cli(path)?;
            print!(
                "{}",
                gen_lua_iife_bundle(&graph, &inference.module_envs, &entry)
            );
        }
        Commands::Lsp => {
            if let Err(err) = hern_lsp::run() {
                eprintln!("LSP error: {}", err);
                std::process::exit(1);
            }
        }
    }
    Ok(())
}

fn parse_file_for_cli(path: &Path) -> Result<hern_core::ast::Program, CliError> {
    let graph = ModuleGraph::new()?;
    parse_file_recovering(path, &graph.prelude)?
        .into_result()
        .map_err(CliError::from)
}

fn analyze_workspace_for_cli(
    path: PathBuf,
) -> Result<(ModuleGraph, hern_core::module::GraphInference, String), CliError> {
    let analysis = analyze_workspace(WorkspaceInputs {
        entry: path,
        overlays: HashMap::new(),
        prelude: None,
    });
    if !analysis.diagnostics.is_empty() {
        return Err(CliError::Diagnostics(analysis.diagnostics));
    }
    let graph = analysis.graph.ok_or_else(|| {
        CliError::Single(CompilerDiagnostic::error(
            None,
            "internal error: workspace analysis did not return a module graph",
        ))
    })?;
    let inference = analysis.inference.ok_or_else(|| {
        CliError::Single(CompilerDiagnostic::error(
            None,
            "internal error: workspace analysis did not return inference results",
        ))
    })?;
    let entry = analysis.entry.ok_or_else(|| {
        CliError::Single(CompilerDiagnostic::error(
            None,
            "internal error: workspace analysis did not return an entry module",
        ))
    })?;
    Ok((graph, inference, entry))
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

fn gen_lua_bundle(
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

fn gen_lua_iife_bundle(
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

const PRELUDE_MODULE: &str = "hern_prelude";

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
