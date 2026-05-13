use clap::{Parser as ClapParser, Subcommand};
use hern_core::analysis::CompilerDiagnostic;
use hern_core::codegen::bundle::{gen_lua_bundle, gen_lua_iife_bundle};
use hern_core::module::{ModuleGraph, parse_file_recovering};
use hern_core::workspace::{WorkspaceInputs, analyze_workspace};
use std::collections::HashMap;
use std::fmt;
use std::path::{Path, PathBuf};

#[derive(ClapParser)]
#[command(name = "hern")]
#[command(about = "Hern language CLI", long_about = None)]
struct Cli {
    #[command(subcommand)]
    command: Option<Commands>,
    /// Path to a Hern file to run. Equivalent to `hern run <path>`.
    path: Option<PathBuf>,
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
    /// Start the interactive Hern REPL
    Repl {
        /// Optional file to load into the REPL before interaction starts
        path: Option<PathBuf>,
    },
    /// Start the Hern language server (LSP)
    Lsp,
}

fn main() {
    let result = run_cli();
    if let Err(err) = &result {
        eprintln!("{}", err);
    }
    if let Some(report) = hern_core::types::perf::report() {
        eprintln!("{}", report);
    }
    if result.is_err() {
        std::process::exit(1);
    }
}

#[derive(Debug)]
enum CliError {
    Single(CompilerDiagnostic),
    Diagnostics(Vec<CompilerDiagnostic>),
    Usage(String),
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
            CliError::Usage(message) => write!(f, "{message}"),
        }
    }
}

impl std::error::Error for CliError {}

fn run_cli() -> Result<(), CliError> {
    let cli = Cli::parse();

    match (cli.command, cli.path) {
        (Some(_), Some(path)) => Err(CliError::Usage(format!(
            "unexpected path argument `{}`; use either `hern <path>` or a subcommand",
            path.display()
        )))?,
        (None, Some(path)) => run_file(path)?,
        (None, None) => Err(CliError::Usage(
            "missing command or path; try `hern --help`".to_string(),
        ))?,
        (Some(Commands::Parse { path }), None) => {
            let program = parse_file_for_cli(&path)?;
            println!("{:#?}", program);
        }
        (Some(Commands::Typecheck { path, dump }), None) => {
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
        (Some(Commands::Lua { path }), None) => {
            let (graph, inference, entry) = analyze_workspace_for_cli(path)?;
            println!("{}", gen_lua_bundle(&graph, &inference.module_envs, &entry));
        }
        (Some(Commands::Run { path }), None) => run_file(path)?,
        (Some(Commands::Bundle { path }), None) => {
            let (graph, inference, entry) = analyze_workspace_for_cli(path)?;
            print!(
                "{}",
                gen_lua_iife_bundle(&graph, &inference.module_envs, &entry)
            );
        }
        (Some(Commands::Repl { path }), None) => {
            let result = match path {
                Some(path) => hern_repl::run_with_path(path),
                None => hern_repl::run(),
            };
            if let Err(err) = result {
                eprintln!("REPL error: {}", err);
                std::process::exit(1);
            }
        }
        (Some(Commands::Lsp), None) => {
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

fn run_file(path: PathBuf) -> Result<(), CliError> {
    let (graph, inference, entry) = analyze_workspace_for_cli(path)?;
    let lua_code = gen_lua_iife_bundle(&graph, &inference.module_envs, &entry);
    hern_repl::exec_lua(&lua_code)
        .map_err(|e| CliError::Single(CompilerDiagnostic::error(None, &e.to_string())))
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn top_level_path_is_run_shorthand() {
        let cli = Cli::try_parse_from(["hern", "script.hern"]).expect("path should parse");

        assert!(cli.command.is_none());
        assert_eq!(cli.path, Some(PathBuf::from("script.hern")));
    }

    #[test]
    fn run_subcommand_still_parses_normally() {
        let cli = Cli::try_parse_from(["hern", "run", "script.hern"]).expect("run should parse");

        match cli.command {
            Some(Commands::Run { path }) => assert_eq!(path, PathBuf::from("script.hern")),
            _ => panic!("expected run command"),
        }
        assert_eq!(cli.path, None);
    }
}
