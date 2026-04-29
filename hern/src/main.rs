use clap::{Parser as ClapParser, Subcommand};
use hern_core::analysis::CompilerDiagnostic;
use hern_core::codegen::bundle::{gen_lua_bundle, gen_lua_iife_bundle};
use hern_core::module::{ModuleGraph, parse_file_recovering};
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
    /// Start the interactive Hern REPL
    Repl {
        /// Optional file to load into the REPL before interaction starts
        path: Option<PathBuf>,
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
        Commands::Repl { path } => {
            let result = match path {
                Some(path) => hern_repl::run_with_path(path),
                None => hern_repl::run(),
            };
            if let Err(err) = result {
                eprintln!("REPL error: {}", err);
                std::process::exit(1);
            }
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
