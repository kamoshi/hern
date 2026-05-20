use clap::{Parser as ClapParser, Subcommand};
use hern_core::analysis::CompilerDiagnostic;
use hern_core::ast::{MacroExpansionInfo, SourceSpan};
use hern_core::codegen::bundle::{gen_lua_bundle, gen_lua_iife_bundle, gen_lua_iife_test_bundle};
use hern_core::module::{ModuleGraph, parse_file_recovering};
use hern_core::workspace::{WorkspaceInputs, analyze_workspace};
use std::collections::HashMap;
use std::fmt;
use std::fs;
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
    /// Expand macros and show generated source
    Expand {
        /// Path to the file to expand
        path: PathBuf,
        /// Show only expansions of this macro name
        #[arg(long = "macro")]
        macro_name: Option<String>,
        /// Show only the expansion whose call contains line:col
        #[arg(long, value_parser = parse_line_col)]
        at: Option<LineCol>,
        /// Show all matching expansions when more than one exists
        #[arg(long)]
        all: bool,
        /// Emit JSON lines instead of text
        #[arg(long)]
        json: bool,
        /// Include call-site and macro-definition span annotations
        #[arg(long)]
        with_origins: bool,
        /// Accepted for scripting; current output has no color
        #[arg(long)]
        no_color: bool,
    },
    /// Run Hern via Lua
    Run {
        /// Path to the file to run
        path: PathBuf,
    },
    /// Run Hern unit tests
    Test {
        /// Path to the file to test
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
        (
            Some(Commands::Expand {
                path,
                macro_name,
                at,
                all,
                json,
                with_origins,
                no_color: _,
            }),
            None,
        ) => {
            print!(
                "{}",
                expand_file_for_cli(ExpandOptions {
                    path,
                    macro_name,
                    at,
                    all,
                    json,
                    with_origins,
                })?
            );
        }
        (Some(Commands::Run { path }), None) => run_file(path)?,
        (Some(Commands::Test { path }), None) => test_file(path)?,
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
        .map_err(|e| CliError::Single(CompilerDiagnostic::error(None, e.to_string())))
}

fn test_file(path: PathBuf) -> Result<(), CliError> {
    let (graph, inference, entry) = analyze_workspace_for_cli(path)?;
    let lua_code = gen_lua_iife_test_bundle(&graph, &inference.module_envs, &entry);
    hern_repl::exec_lua(&lua_code)
        .map_err(|e| CliError::Single(CompilerDiagnostic::error(None, e.to_string())))
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct LineCol {
    line: usize,
    col: usize,
}

#[derive(Debug)]
struct ExpandOptions {
    path: PathBuf,
    macro_name: Option<String>,
    at: Option<LineCol>,
    all: bool,
    json: bool,
    with_origins: bool,
}

#[derive(Debug)]
struct ExpansionDisplay {
    module_name: String,
    module_path: PathBuf,
    original_call: String,
    info: MacroExpansionInfo,
}

fn parse_line_col(input: &str) -> Result<LineCol, String> {
    let Some((line, col)) = input.split_once(':') else {
        return Err("expected line:col".to_string());
    };
    let line = line
        .parse::<usize>()
        .map_err(|_| "line must be a positive integer".to_string())?;
    let col = col
        .parse::<usize>()
        .map_err(|_| "column must be a positive integer".to_string())?;
    if line == 0 || col == 0 {
        return Err("line and column are 1-based and must be positive".to_string());
    }
    Ok(LineCol { line, col })
}

fn expand_file_for_cli(options: ExpandOptions) -> Result<String, CliError> {
    let (graph, _entry) = ModuleGraph::load_entry(&options.path)?;
    let expansions = collect_expansion_displays(&graph, &options)?;

    if expansions.is_empty() {
        return Ok("No macro expansions.\n".to_string());
    }
    if !options.all && options.macro_name.is_none() && options.at.is_none() && expansions.len() > 1
    {
        return Err(CliError::Usage(format!(
            "found {} macro expansions; pass `--all`, `--macro name`, or `--at line:col`",
            expansions.len()
        )));
    }

    if options.json {
        Ok(expansions
            .iter()
            .map(|expansion| expansion_json(expansion, options.with_origins))
            .collect::<Vec<_>>()
            .join("\n")
            + "\n")
    } else {
        Ok(expansions
            .iter()
            .map(|expansion| expansion_text(expansion, options.with_origins))
            .collect::<Vec<_>>()
            .join("\n\n")
            + "\n")
    }
}

fn collect_expansion_displays(
    graph: &ModuleGraph,
    options: &ExpandOptions,
) -> Result<Vec<ExpansionDisplay>, CliError> {
    let mut out = Vec::new();
    for module_name in &graph.order {
        let Some(program) = graph.modules.get(module_name) else {
            continue;
        };
        let Some(module_path) = graph.paths.get(module_name) else {
            continue;
        };
        let source = fs::read_to_string(module_path).map_err(|err| {
            CliError::Single(
                CompilerDiagnostic::error(
                    None,
                    format!("failed to read {}: {err}", module_path.display()),
                )
                .with_source(hern_core::analysis::DiagnosticSource::Path(
                    module_path.clone(),
                )),
            )
        })?;
        for info in &program.macro_expansions {
            if let Some(name) = &options.macro_name
                && &info.macro_name != name
            {
                continue;
            }
            if let Some(at) = options.at
                && !span_contains_line_col(info.call_span, at)
            {
                continue;
            }
            out.push(ExpansionDisplay {
                module_name: module_name.clone(),
                module_path: module_path.clone(),
                original_call: source_excerpt_for_span(&source, info.call_span),
                info: info.clone(),
            });
        }
    }
    Ok(out)
}

fn span_contains_line_col(span: SourceSpan, at: LineCol) -> bool {
    (span.start_line, span.start_col) <= (at.line, at.col)
        && (at.line, at.col) < (span.end_line, span.end_col)
}

fn source_excerpt_for_span(source: &str, span: SourceSpan) -> String {
    let mut out = String::new();
    for (line_index, line) in source.lines().enumerate() {
        let line_no = line_index + 1;
        if line_no < span.start_line || line_no > span.end_line {
            continue;
        }
        let start = if line_no == span.start_line {
            span.start_col.saturating_sub(1)
        } else {
            0
        };
        let end = if line_no == span.end_line {
            span.end_col.saturating_sub(1)
        } else {
            line.len()
        };
        let start = start.min(line.len());
        let end = end.min(line.len()).max(start);
        if !out.is_empty() {
            out.push('\n');
        }
        out.push_str(&line[start..end]);
    }
    out
}

fn expansion_text(expansion: &ExpansionDisplay, with_origins: bool) -> String {
    let mut out = String::new();
    out.push_str(&format!(
        "{}! in {}:{}:{}\n",
        expansion.info.macro_name,
        expansion.module_path.display(),
        expansion.info.call_span.start_line,
        expansion.info.call_span.start_col
    ));
    if with_origins {
        out.push_str(&format!(
            "module: {}\ncall span: {}\ndefinition span: {}\n",
            expansion.module_name,
            format_span(expansion.info.call_span),
            format_span(expansion.info.definition_span)
        ));
    }
    out.push_str("original:\n");
    out.push_str(&indent_block(&expansion.original_call));
    out.push_str("\nexpanded:\n");
    out.push_str(&indent_block(&expansion.info.generated_source_excerpt));
    out
}

fn expansion_json(expansion: &ExpansionDisplay, with_origins: bool) -> String {
    let mut fields = vec![
        format!("\"module\":{}", json_string(&expansion.module_name)),
        format!(
            "\"path\":{}",
            json_string(&expansion.module_path.display().to_string())
        ),
        format!("\"macro\":{}", json_string(&expansion.info.macro_name)),
        format!("\"original\":{}", json_string(&expansion.original_call)),
        format!(
            "\"expanded\":{}",
            json_string(&expansion.info.generated_source_excerpt)
        ),
    ];
    if with_origins {
        fields.push(format!(
            "\"call_span\":{}",
            json_span(expansion.info.call_span)
        ));
        fields.push(format!(
            "\"definition_span\":{}",
            json_span(expansion.info.definition_span)
        ));
    }
    format!("{{{}}}", fields.join(","))
}

fn indent_block(text: &str) -> String {
    text.lines()
        .map(|line| format!("  {line}"))
        .collect::<Vec<_>>()
        .join("\n")
}

fn format_span(span: SourceSpan) -> String {
    format!(
        "{}:{}-{}:{}",
        span.start_line, span.start_col, span.end_line, span.end_col
    )
}

fn json_span(span: SourceSpan) -> String {
    format!(
        "{{\"start_line\":{},\"start_col\":{},\"end_line\":{},\"end_col\":{}}}",
        span.start_line, span.start_col, span.end_line, span.end_col
    )
}

fn json_string(value: &str) -> String {
    let mut out = String::from("\"");
    for ch in value.chars() {
        match ch {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            ch if ch.is_control() => out.push_str(&format!("\\u{:04x}", ch as u32)),
            ch => out.push(ch),
        }
    }
    out.push('"');
    out
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

    #[test]
    fn test_subcommand_parses_normally() {
        let cli = Cli::try_parse_from(["hern", "test", "script.hern"]).expect("test should parse");

        match cli.command {
            Some(Commands::Test { path }) => assert_eq!(path, PathBuf::from("script.hern")),
            _ => panic!("expected test command"),
        }
        assert_eq!(cli.path, None);
    }

    #[test]
    fn expand_subcommand_parses_filters() {
        let cli = Cli::try_parse_from([
            "hern",
            "expand",
            "script.hern",
            "--macro",
            "unless",
            "--at",
            "3:5",
            "--json",
            "--with-origins",
        ])
        .expect("expand should parse");

        match cli.command {
            Some(Commands::Expand {
                path,
                macro_name,
                at,
                json,
                with_origins,
                ..
            }) => {
                assert_eq!(path, PathBuf::from("script.hern"));
                assert_eq!(macro_name, Some("unless".to_string()));
                assert_eq!(at, Some(LineCol { line: 3, col: 5 }));
                assert!(json);
                assert!(with_origins);
            }
            _ => panic!("expected expand command"),
        }
        assert_eq!(cli.path, None);
    }

    #[test]
    fn expand_file_reports_original_and_generated_source() {
        let dir = std::env::temp_dir().join(format!("hern-expand-test-{}", std::process::id()));
        std::fs::create_dir_all(&dir).expect("temp dir should be created");
        let path = dir.join("main.hern");
        std::fs::write(
            &path,
            r#"macro swap_add(input: Syntax) -> MacroResult(Syntax) {
  match input {
    '{$lhs:expr, $rhs:expr} -> Ok('{ $rhs + $lhs }),
    _ -> Err(MacroError("bad input")),
  }
}

print(to_string(swap_add!(1, 2)));
"#,
        )
        .expect("test file should be written");

        let output = expand_file_for_cli(ExpandOptions {
            path,
            macro_name: Some("swap_add".to_string()),
            at: None,
            all: false,
            json: false,
            with_origins: true,
        })
        .expect("expand output should be produced");

        assert!(output.contains("swap_add! in "));
        assert!(output.contains("original:\n  swap_add!(1, 2)"));
        assert!(output.contains("expanded:\n  {2 + 1}"));
        assert!(output.contains("definition span:"));
    }
}
