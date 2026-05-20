use crate::analysis::{CompilerDiagnostic, DiagnosticSource, analyze_prelude};
use crate::ast::{
    Expr, ExprKind, NodeId, Param, Pattern, Program, SourceSpan, Stmt, TraitDef, walk_program_exprs,
};
use crate::derive::expand_derives;
use crate::macros::expand_macros;
use crate::pipeline::{
    AnalysisOutput, parse_source, parse_source_recovering, reassociate_with_program,
};
use crate::types::infer::{Infer, TypeEnv, VariantEnv};
use crate::types::{
    BindingCapabilities, CallableCapabilities, InherentMethodScheme, Scheme, SyntaxCaptureInfo, Ty,
    trait_dict_indexes, trait_impl_arg_keys_from_ast, trait_impl_dict_name_for_indexes,
    type_syntax::exact_impl_target_key_from_ast,
};
use std::collections::hash_map::DefaultHasher;
use std::collections::{HashMap, HashSet};
use std::fs;
use std::hash::{Hash, Hasher};
use std::path::{Path, PathBuf};

const PRELUDE_OWNER: &str = "<prelude>";
const HERN_IMPORT_PREFIX: &str = "hern:";

#[derive(Clone)]
pub struct ModuleGraph {
    pub prelude: Program,
    pub modules: HashMap<String, Program>,
    pub paths: HashMap<String, PathBuf>,
    pub order: Vec<String>,
    pub no_prelude_modules: HashSet<String>,
    loading: HashSet<PathBuf>,
    overlays: HashMap<PathBuf, String>,
}

#[derive(Clone, Default)]
pub struct GraphInference {
    pub import_types: HashMap<String, Ty>,
    pub import_schemes: HashMap<String, HashMap<String, Scheme>>,
    pub envs: HashMap<String, TypeEnv>,
    pub variant_envs: HashMap<String, VariantEnv>,
    pub module_envs: HashMap<String, ModuleEnv>,
    pub module_metadata: HashMap<String, ModuleInferenceMetadata>,
}

#[derive(Clone, Default)]
pub struct ModuleInferenceMetadata {
    pub expr_types: HashMap<NodeId, Ty>,
    pub symbol_types: HashMap<NodeId, Ty>,
    pub binding_types: HashMap<SourceSpan, Ty>,
    pub syntax_captures: HashMap<SourceSpan, SyntaxCaptureInfo>,
    pub definition_schemes: HashMap<SourceSpan, Scheme>,
    pub binding_capabilities: HashMap<SourceSpan, BindingCapabilities>,
    pub callable_capabilities: HashMap<NodeId, CallableCapabilities>,
    pub fresh_place_exprs: HashSet<NodeId>,
}

#[derive(Clone)]
pub struct LoadedModuleGraph {
    pub graph: ModuleGraph,
    pub entry: String,
}

#[derive(Clone, Default)]
pub struct ModuleEnv {
    types: HashMap<String, EnvType>,
    traits: HashMap<String, EnvTrait>,
    ops: HashMap<String, EnvOp>,
    impls: HashMap<ImplKey, EnvImpl>,
    inherent_impls: HashMap<String, EnvInherentImpl>,
}

#[derive(Clone)]
struct EnvType {
    owner: String,
}

#[derive(Clone)]
struct EnvTrait {
    def: TraitDef,
    owner: String,
}

#[derive(Clone)]
struct EnvOp {
    trait_name: String,
    owner: String,
}

#[derive(Clone)]
struct EnvImpl {
    dict_name: String,
    scheme: Option<Scheme>,
    owner: String,
}

#[derive(Clone)]
struct EnvInherentImpl {
    methods: HashMap<String, InherentMethodScheme>,
    dict_name: String,
    owner: String,
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
struct ImplKey {
    trait_name: String,
    args: Vec<String>,
}

struct InferScope {
    type_names: HashSet<String>,
    traits: HashMap<String, TraitDef>,
    ops: HashMap<String, String>,
    inherent_methods: HashMap<String, HashMap<String, InherentMethodScheme>>,
}

impl ModuleGraph {
    /// Creates an empty graph, loading the built-in prelude.
    ///
    /// Fail-fast: returns an error if the prelude fails to analyze.
    pub fn new() -> Result<Self, CompilerDiagnostic> {
        Self::new_with_overlays(HashMap::new())
    }

    /// Creates an empty graph with in-memory source overlays, loading the built-in prelude.
    ///
    /// Fail-fast: returns an error if the prelude fails to analyze.
    pub fn new_with_overlays(
        overlays: HashMap<PathBuf, String>,
    ) -> Result<Self, CompilerDiagnostic> {
        let prelude = analyze_prelude()?.program;
        Ok(Self::new_with_prelude_and_overlays(prelude, overlays))
    }

    /// Creates an empty graph with a pre-analyzed prelude and in-memory source overlays.
    pub fn new_with_prelude_and_overlays(
        prelude: Program,
        overlays: HashMap<PathBuf, String>,
    ) -> Self {
        let overlays = normalize_overlays(overlays);
        Self {
            prelude,
            modules: HashMap::new(),
            paths: HashMap::new(),
            order: Vec::new(),
            no_prelude_modules: HashSet::new(),
            loading: HashSet::new(),
            overlays,
        }
    }

    /// Loads an entry module and all its transitive imports from disk, using a pre-analyzed
    /// prelude and in-memory overlays.
    ///
    /// Fail-fast: returns the first diagnostic (parse, import resolution, or IO error).
    /// Use [`load_entry_with_prelude_and_overlays_recovering`] for partial graph loading.
    pub fn load_entry_with_prelude_and_overlays(
        path: &Path,
        prelude: Program,
        overlays: HashMap<PathBuf, String>,
    ) -> Result<(Self, String), CompilerDiagnostic> {
        let mut graph = Self::new_with_prelude_and_overlays(prelude, overlays);
        let entry = graph.load_module(path)?;
        Ok((graph, entry))
    }

    /// Loads an entry module and all its transitive imports from disk, using in-memory overlays.
    ///
    /// Fail-fast: returns the first diagnostic. Use [`load_entry_with_overlays_recovering`] for
    /// partial graph loading.
    pub fn load_entry_with_overlays(
        path: &Path,
        overlays: HashMap<PathBuf, String>,
    ) -> Result<(Self, String), CompilerDiagnostic> {
        let mut graph = Self::new_with_overlays(overlays)?;
        let entry = graph.load_module(path)?;
        Ok((graph, entry))
    }

    /// Loads an entry module and all its transitive imports from disk.
    ///
    /// Fail-fast: returns the first diagnostic. Use [`load_entry_recovering`] for partial graph
    /// loading.
    pub fn load_entry(path: &Path) -> Result<(Self, String), CompilerDiagnostic> {
        let mut graph = Self::new()?;
        let entry = graph.load_module(path)?;
        Ok((graph, entry))
    }

    /// Loads an entry module and its transitive imports with parse-level recovery.
    ///
    /// Parse errors in individual modules are collected rather than failing immediately. Prelude
    /// analysis is still fail-fast: an error there stops loading entirely.
    pub fn load_entry_recovering(
        path: &Path,
    ) -> Result<AnalysisOutput<LoadedModuleGraph>, CompilerDiagnostic> {
        Self::load_entry_with_overlays_recovering(path, HashMap::new())
    }

    /// Loads an entry module and its transitive imports with parse-level recovery and in-memory
    /// overlays.
    ///
    /// Prelude analysis is still fail-fast. Parse errors in other modules are collected.
    pub fn load_entry_with_overlays_recovering(
        path: &Path,
        overlays: HashMap<PathBuf, String>,
    ) -> Result<AnalysisOutput<LoadedModuleGraph>, CompilerDiagnostic> {
        let prelude = analyze_prelude()?.program;
        Ok(Self::load_entry_with_prelude_and_overlays_recovering(
            path, prelude, overlays,
        ))
    }

    /// Loads an entry module and its transitive imports with parse-level recovery, using a
    /// pre-analyzed prelude and in-memory overlays.
    ///
    /// Returns a partial graph when module loading reaches parse/import recovery; path, read, or
    /// lex failures can still prevent useful module contents from being available. Prefer this
    /// over [`load_entry_with_prelude_and_overlays`] in LSP and watch-mode contexts.
    pub fn load_entry_with_prelude_and_overlays_recovering(
        path: &Path,
        prelude: Program,
        overlays: HashMap<PathBuf, String>,
    ) -> AnalysisOutput<LoadedModuleGraph> {
        let mut graph = Self::new_with_prelude_and_overlays(prelude, overlays);
        let (entry, diagnostics) = graph.load_module_recovering(path);
        let loaded = LoadedModuleGraph { graph, entry };
        if diagnostics.is_empty() {
            AnalysisOutput::success(loaded)
        } else {
            AnalysisOutput::partial(loaded, diagnostics)
        }
    }

    pub fn module(&self, name: &str) -> Option<&Program> {
        self.modules.get(name)
    }

    pub fn module_path(&self, name: &str) -> Option<&Path> {
        self.paths.get(name).map(PathBuf::as_path)
    }

    pub fn module_name_for_path(&self, path: &Path) -> Option<&str> {
        let normalized = self.normalize_load_path(path).ok();
        self.paths
            .iter()
            .find(|(_, module_path)| {
                normalized.as_ref().map_or_else(
                    || module_path.as_path() == path,
                    |path| *module_path == path,
                )
            })
            .map(|(name, _)| name.as_str())
    }

    pub fn module_for_path(&self, path: &Path) -> Option<(&str, &Program)> {
        let name = self.module_name_for_path(path)?;
        let program = self.module(name)?;
        Some((name, program))
    }

    pub fn load_module(&mut self, path: &Path) -> Result<String, CompilerDiagnostic> {
        let path = self.normalize_load_path(path)?;
        let name = module_name(&path);
        if self.modules.contains_key(&name) {
            return Ok(name);
        }
        if !self.loading.insert(path.clone()) {
            return Err(CompilerDiagnostic::error(
                None,
                format!("circular import involving {}", path.display()),
            )
            .with_source(DiagnosticSource::Path(path)));
        }

        let loaded = (|| {
            let content = self.read_source(&path)?;
            let mut program = parse_source(&content)
                .map_err(|err| err.with_source_if_absent(DiagnosticSource::Path(path.clone())))?;
            expand_macros(&mut program)
                .map_err(|err| err.with_source_if_absent(DiagnosticSource::Path(path.clone())))?;
            let base_dir = path
                .parent()
                .unwrap_or_else(|| Path::new("."))
                .to_path_buf();
            resolve_imports_in_program(&mut program, &base_dir, self)
                .map_err(|err| err.with_source_if_absent(DiagnosticSource::Path(path.clone())))?;
            expand_derives(&mut program);
            if program
                .inner_attrs
                .iter()
                .any(|a| a == "no_implicit_prelude")
            {
                reassociate_with_program(
                    &mut program,
                    &Program {
                        stmts: vec![],
                        inner_attrs: vec![],
                    },
                )
                .map_err(|err| err.with_source_if_absent(DiagnosticSource::Path(path.clone())))?;
            } else {
                reassociate_with_program(&mut program, &self.prelude).map_err(|err| {
                    err.with_source_if_absent(DiagnosticSource::Path(path.clone()))
                })?;
            }
            Ok(program)
        })();
        self.loading.remove(&path);

        let program = loaded?;
        if program
            .inner_attrs
            .iter()
            .any(|a| a == "no_implicit_prelude")
        {
            self.no_prelude_modules.insert(name.clone());
        }
        self.paths.insert(name.clone(), path);
        self.modules.insert(name.clone(), program);
        self.order.push(name.clone());
        Ok(name)
    }

    fn load_module_recovering(&mut self, path: &Path) -> (String, Vec<CompilerDiagnostic>) {
        let path = match self.normalize_load_path(path) {
            Ok(path) => path,
            Err(diagnostic) => return (module_name(path), vec![diagnostic]),
        };
        let name = module_name(&path);
        if self.modules.contains_key(&name) {
            return (name, Vec::new());
        }
        if !self.loading.insert(path.clone()) {
            return (
                name,
                vec![
                    CompilerDiagnostic::error(
                        None,
                        format!("circular import involving {}", path.display()),
                    )
                    .with_source(DiagnosticSource::Path(path)),
                ],
            );
        }

        let source = DiagnosticSource::Path(path.clone());
        let loaded = (|| {
            let content = self.read_source(&path)?;
            let mut parsed = parse_source_recovering(&content)
                .map_err(|diagnostic| diagnostic.with_source_if_absent(source.clone()))?;
            for diagnostic in &mut parsed.diagnostics {
                if diagnostic.source.is_none() {
                    diagnostic.source = Some(source.clone());
                }
            }

            let base_dir = path
                .parent()
                .unwrap_or_else(|| Path::new("."))
                .to_path_buf();
            let mut diagnostics = parsed.diagnostics;
            if let Err(err) = expand_macros(&mut parsed.program) {
                diagnostics.push(err.with_source_if_absent(source.clone()));
            }
            diagnostics.extend(resolve_imports_in_program_recovering(
                &mut parsed.program,
                &base_dir,
                self,
                DiagnosticSource::Path(path.clone()),
            ));
            expand_derives(&mut parsed.program);
            if parsed
                .program
                .inner_attrs
                .iter()
                .any(|a| a == "no_implicit_prelude")
            {
                if let Err(err) = reassociate_with_program(
                    &mut parsed.program,
                    &Program {
                        stmts: vec![],
                        inner_attrs: vec![],
                    },
                ) {
                    diagnostics
                        .push(err.with_source_if_absent(DiagnosticSource::Path(path.clone())));
                }
            } else {
                if let Err(err) = reassociate_with_program(&mut parsed.program, &self.prelude) {
                    diagnostics
                        .push(err.with_source_if_absent(DiagnosticSource::Path(path.clone())));
                }
            }
            Ok((parsed.program, diagnostics))
        })();

        self.loading.remove(&path);

        let (program, diagnostics) = match loaded {
            Ok(loaded) => loaded,
            Err(diagnostic) => return (name, vec![diagnostic]),
        };
        if program
            .inner_attrs
            .iter()
            .any(|a| a == "no_implicit_prelude")
        {
            self.no_prelude_modules.insert(name.clone());
        }
        self.paths.insert(name.clone(), path);
        self.modules.insert(name.clone(), program);
        self.order.push(name.clone());
        (name, diagnostics)
    }

    fn read_source(&self, path: &Path) -> Result<String, CompilerDiagnostic> {
        if let Some(source) = self.overlays.get(path) {
            return Ok(source.clone());
        }
        fs::read_to_string(path).map_err(|err| {
            CompilerDiagnostic::error_in(
                DiagnosticSource::Path(path.to_path_buf()),
                None,
                format!("error reading file {}: {}", path.display(), err),
            )
        })
    }

    fn normalize_load_path(&self, path: &Path) -> Result<PathBuf, CompilerDiagnostic> {
        match fs::canonicalize(path) {
            Ok(path) => Ok(path),
            Err(err) => {
                let overlay_path = normalize_overlay_path(path);
                if self.overlays.contains_key(&overlay_path) {
                    Ok(overlay_path)
                } else {
                    Err(CompilerDiagnostic::error_in(
                        DiagnosticSource::Path(path.to_path_buf()),
                        None,
                        format!("error resolving file {}: {}", path.display(), err),
                    ))
                }
            }
        }
    }

    fn resolve_import_path(
        &self,
        base_dir: &Path,
        spec: &str,
    ) -> Result<PathBuf, CompilerDiagnostic> {
        let mut path = if let Some(std_spec) = spec.strip_prefix(HERN_IMPORT_PREFIX) {
            resolve_std_import_path(std_spec)?
        } else {
            base_dir.join(spec)
        };
        if path.extension().is_none() {
            path.set_extension("hern");
        }
        let std_root = if spec.starts_with(HERN_IMPORT_PREFIX) {
            Some(std_root()?)
        } else {
            None
        };
        match fs::canonicalize(&path) {
            Ok(path) => {
                if let Some(std_root) = std_root
                    && !path.starts_with(std_root)
                {
                    return Err(CompilerDiagnostic::error(
                        None,
                        format!("invalid Hern std import `{}`", spec),
                    ));
                }
                Ok(path)
            }
            Err(err) => {
                let overlay_path = normalize_overlay_path(&path);
                if self.overlays.contains_key(&overlay_path) {
                    Ok(overlay_path)
                } else {
                    Err(CompilerDiagnostic::error(
                        None,
                        format!("error resolving file {}: {}", path.display(), err),
                    ))
                }
            }
        }
    }
}

fn resolve_std_import_path(spec: &str) -> Result<PathBuf, CompilerDiagnostic> {
    if spec.is_empty() || spec.starts_with('/') || spec.contains('\\') {
        return Err(CompilerDiagnostic::error(
            None,
            format!("invalid Hern std import `{}{}`", HERN_IMPORT_PREFIX, spec),
        ));
    }
    let path = Path::new(spec);
    if path
        .components()
        .any(|component| !matches!(component, std::path::Component::Normal(_)))
    {
        return Err(CompilerDiagnostic::error(
            None,
            format!("invalid Hern std import `{}{}`", HERN_IMPORT_PREFIX, spec),
        ));
    }
    Ok(std_root()?.join(path))
}

fn std_root() -> Result<PathBuf, CompilerDiagnostic> {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../std");
    fs::canonicalize(&root).map_err(|err| {
        CompilerDiagnostic::error(
            None,
            format!(
                "error resolving Hern std directory {}: {}",
                root.display(),
                err
            ),
        )
    })
}

impl GraphInference {
    pub fn metadata_for_module(&self, name: &str) -> Option<&ModuleInferenceMetadata> {
        self.module_metadata.get(name)
    }

    pub fn expr_types_for_module(&self, name: &str) -> Option<&HashMap<NodeId, Ty>> {
        self.metadata_for_module(name)
            .map(|metadata| &metadata.expr_types)
    }

    pub fn symbol_types_for_module(&self, name: &str) -> Option<&HashMap<NodeId, Ty>> {
        self.metadata_for_module(name)
            .map(|metadata| &metadata.symbol_types)
    }

    pub fn binding_types_for_module(&self, name: &str) -> Option<&HashMap<SourceSpan, Ty>> {
        self.metadata_for_module(name)
            .map(|metadata| &metadata.binding_types)
    }

    pub fn definition_schemes_for_module(
        &self,
        name: &str,
    ) -> Option<&HashMap<SourceSpan, Scheme>> {
        self.metadata_for_module(name)
            .map(|metadata| &metadata.definition_schemes)
    }

    pub fn syntax_captures_for_module(
        &self,
        name: &str,
    ) -> Option<&HashMap<SourceSpan, SyntaxCaptureInfo>> {
        self.metadata_for_module(name)
            .map(|metadata| &metadata.syntax_captures)
    }

    pub fn binding_capabilities_for_module(
        &self,
        name: &str,
    ) -> Option<&HashMap<SourceSpan, BindingCapabilities>> {
        self.metadata_for_module(name)
            .map(|metadata| &metadata.binding_capabilities)
    }

    pub fn callable_capabilities_for_module(
        &self,
        name: &str,
    ) -> Option<&HashMap<NodeId, CallableCapabilities>> {
        self.metadata_for_module(name)
            .map(|metadata| &metadata.callable_capabilities)
    }

    pub fn fresh_place_exprs_for_module(&self, name: &str) -> Option<&HashSet<NodeId>> {
        self.metadata_for_module(name)
            .map(|metadata| &metadata.fresh_place_exprs)
    }

    pub fn env_for_module(&self, name: &str) -> Option<&TypeEnv> {
        self.envs.get(name)
    }

    pub fn module_env_for_module(&self, name: &str) -> Option<&ModuleEnv> {
        self.module_envs.get(name)
    }

    pub fn variant_env_for_module(&self, name: &str) -> Option<&VariantEnv> {
        self.variant_envs.get(name)
    }
}

pub fn parse_file(path: &Path, prelude: &Program) -> Result<Program, CompilerDiagnostic> {
    let source = DiagnosticSource::Path(path.to_path_buf());
    let content = fs::read_to_string(path).map_err(|err| {
        CompilerDiagnostic::error_in(
            source.clone(),
            None,
            format!("error reading file {}: {}", path.display(), err),
        )
    })?;
    let mut program =
        parse_source(&content).map_err(|err| err.with_source_if_absent(source.clone()))?;
    expand_macros(&mut program)?;
    expand_derives(&mut program);
    reassociate_with_program(&mut program, prelude)?;
    Ok(program)
}

pub fn parse_file_recovering(
    path: &Path,
    prelude: &Program,
) -> Result<AnalysisOutput<Program>, CompilerDiagnostic> {
    let source = DiagnosticSource::Path(path.to_path_buf());
    let content = fs::read_to_string(path).map_err(|err| {
        CompilerDiagnostic::error_in(
            source.clone(),
            None,
            format!("error reading file {}: {}", path.display(), err),
        )
    })?;
    let mut parsed = parse_source_recovering(&content)
        .map_err(|err| err.with_source_if_absent(source.clone()))?;
    for diagnostic in &mut parsed.diagnostics {
        if diagnostic.source.is_none() {
            diagnostic.source = Some(source.clone());
        }
    }
    if !parsed.diagnostics.is_empty() {
        return Ok(AnalysisOutput::diagnostics(parsed.diagnostics));
    }

    if let Err(err) = expand_macros(&mut parsed.program) {
        return Ok(AnalysisOutput::diagnostics(vec![
            err.with_source_if_absent(source),
        ]));
    }
    expand_derives(&mut parsed.program);
    if let Err(err) = reassociate_with_program(&mut parsed.program, prelude) {
        return Ok(AnalysisOutput::diagnostics(vec![
            err.with_source_if_absent(source),
        ]));
    }
    Ok(AnalysisOutput::success(parsed.program))
}

/// Runs type inference on all modules in `graph`.
///
/// Fail-fast wrapper around [`infer_graph_collecting`]: returns the first diagnostic on failure.
/// Use [`infer_graph_collecting`] in LSP/watch-mode contexts to collect all diagnostics.
pub fn infer_graph(graph: &mut ModuleGraph) -> Result<GraphInference, CompilerDiagnostic> {
    let output = infer_graph_collecting(graph);
    if output.diagnostics.is_empty() {
        Ok(output
            .value
            .expect("successful graph inference should return a value"))
    } else {
        Err(output
            .diagnostics
            .into_iter()
            .next()
            .expect("diagnostic result should include a diagnostic"))
    }
}

/// Runs type inference on all modules in `graph`, collecting all diagnostics.
///
/// Modules whose imports have type errors are skipped to avoid cascaded diagnostics rather than
/// stopping inference entirely. Prefer this over [`infer_graph`] in LSP and watch-mode contexts.
pub fn infer_graph_collecting(graph: &mut ModuleGraph) -> AnalysisOutput<GraphInference> {
    let mut infer = Infer::new();
    let mut prelude_program = graph.prelude.clone();
    let prelude_inference =
        match infer.infer_program_with_seed_and_types(&mut prelude_program, &[], None) {
            Ok(inference) => inference,
            Err(err) => {
                return AnalysisOutput::diagnostics(vec![CompilerDiagnostic::error_in(
                    DiagnosticSource::Prelude,
                    err.span,
                    format!("type error in <prelude>: {}", err),
                )]);
            }
        };
    let prelude_env = prelude_inference.env.clone();
    graph.prelude = prelude_program;

    let mut prelude_module_env = match module_env_from_program(&graph.prelude, PRELUDE_OWNER) {
        Ok(env) => env,
        Err(err) => {
            return AnalysisOutput::diagnostics(vec![
                err.with_source_if_absent(DiagnosticSource::Prelude),
            ]);
        }
    };
    prelude_module_env.attach_trait_impl_schemes(&prelude_env);
    prelude_module_env.attach_inherent_method_schemes(&prelude_inference.inherent_method_schemes);

    let empty_module_env = ModuleEnv::default();
    let mut diagnostics = Vec::new();
    let mut unavailable_modules = HashSet::new();
    let mut result = GraphInference::default();
    for name in graph.order.clone() {
        let source = diagnostic_source_for_module(graph, &name);
        let imports = graph
            .modules
            .get(&name)
            .map(collect_imports_in_program)
            .unwrap_or_default();
        if imports
            .iter()
            .any(|import| unavailable_modules.contains(import))
        {
            unavailable_modules.insert(name);
            continue;
        }

        let is_no_prelude = graph.no_prelude_modules.contains(&name);
        let effective_prelude_env = if is_no_prelude {
            &empty_module_env
        } else {
            &prelude_module_env
        };
        let module_env =
            match build_module_env(graph, &result.module_envs, effective_prelude_env, &name)
                .map_err(|err| err.with_source_if_absent(source.clone()))
            {
                Ok(env) => env,
                Err(diagnostic) => {
                    diagnostics.push(diagnostic);
                    unavailable_modules.insert(name);
                    continue;
                }
            };
        let infer_scope = module_env.to_infer_scope();
        infer.set_type_scope(infer_scope.type_names);
        infer.set_trait_scope(infer_scope.traits, infer_scope.ops);
        infer.set_inherent_scope(infer_scope.inherent_methods);
        infer.set_known_impl_dicts(module_env.all_dict_names());
        infer.set_known_impl_schemes(module_env.all_trait_impl_schemes());
        infer.set_import_types(result.import_types.clone());
        infer.set_import_schemes(result.import_schemes.clone());
        let program = match graph.modules.get_mut(&name) {
            Some(program) => program,
            None => {
                diagnostics.push(CompilerDiagnostic::error_in(
                    source,
                    None,
                    format!("internal error: loaded module `{}` missing", name),
                ));
                unavailable_modules.insert(name);
                continue;
            }
        };
        let (prelude_stmts, prelude_type_env): (&[_], _) = if is_no_prelude {
            (&[], None)
        } else {
            (&graph.prelude.stmts, Some(&prelude_env))
        };
        let (inference, module_errors) =
            infer.infer_program_collecting(program, prelude_stmts, prelude_type_env);
        let has_errors = !module_errors.is_empty();

        // Keep best-effort per-module state even when the module had its own diagnostics so LSP
        // features can still use surviving declarations. Importers are still blocked below by
        // marking the module unavailable, so partial state never becomes a valid dependency.
        result
            .import_types
            .insert(name.clone(), inference.value_ty.clone());
        result.import_schemes.insert(
            name.clone(),
            export_schemes_from_program(program, &inference.env),
        );
        let mut module_env = module_env;
        module_env.attach_trait_impl_schemes(&inference.env);
        module_env.attach_inherent_method_schemes(&inference.inherent_method_schemes);
        result.envs.insert(name.clone(), inference.env);
        result
            .variant_envs
            .insert(name.clone(), inference.variant_env);
        result.module_envs.insert(name.clone(), module_env);
        result.module_metadata.insert(
            name.clone(),
            ModuleInferenceMetadata {
                expr_types: inference.expr_types,
                symbol_types: inference.symbol_types,
                binding_types: inference.binding_types,
                syntax_captures: inference.syntax_captures,
                definition_schemes: inference.definition_schemes,
                binding_capabilities: inference.binding_capabilities,
                callable_capabilities: inference.callable_capabilities,
                fresh_place_exprs: inference.fresh_place_exprs,
            },
        );

        if has_errors {
            diagnostics.extend(
                module_errors
                    .into_iter()
                    .map(|err| module_type_diagnostic(graph, &name, source.clone(), err)),
            );
            unavailable_modules.insert(name);
        }
    }

    if diagnostics.is_empty() {
        AnalysisOutput::success(result)
    } else {
        AnalysisOutput::partial(result, diagnostics)
    }
}

fn module_type_diagnostic(
    graph: &ModuleGraph,
    name: &str,
    source: DiagnosticSource,
    err: crate::types::error::SpannedTypeError,
) -> CompilerDiagnostic {
    let path = graph
        .paths
        .get(name)
        .map(|p| p.display().to_string())
        .unwrap_or_else(|| name.to_string());
    CompilerDiagnostic::error_in(source, err.span, format!("type error in {}: {}", path, err))
}

fn export_schemes_from_program(program: &Program, env: &TypeEnv) -> HashMap<String, Scheme> {
    let Some(Stmt::Expr(expr)) = program.stmts.last() else {
        return HashMap::new();
    };
    let ExprKind::Record(entries) = &expr.kind else {
        return HashMap::new();
    };
    let mut schemes = HashMap::new();
    for entry in entries {
        let crate::ast::RecordEntry::Field(field_name, value) = entry else {
            continue;
        };
        let ExprKind::Ident(binding_name) = &value.kind else {
            continue;
        };
        if let Some(info) = env.get(binding_name) {
            schemes.insert(field_name.clone(), info.scheme.clone());
        }
    }
    schemes
}

pub fn collect_imports_in_program(program: &Program) -> Vec<String> {
    let mut imports = collect_imports_with_spans(program)
        .into_iter()
        .map(|import| import.module)
        .collect::<Vec<_>>();
    imports.sort();
    imports.dedup();
    imports
}

struct ImportRef {
    module: String,
    span: SourceSpan,
}

fn collect_imports_with_spans(program: &Program) -> Vec<ImportRef> {
    let mut imports = Vec::new();
    walk_program_exprs(program, &mut |expr| {
        if let ExprKind::Import(name) = &expr.kind {
            imports.push(ImportRef {
                module: name.clone(),
                span: expr.span,
            });
        }
    });
    imports.sort_by(|a, b| {
        a.module
            .cmp(&b.module)
            .then(a.span.start_line.cmp(&b.span.start_line))
            .then(a.span.start_col.cmp(&b.span.start_col))
    });
    imports.dedup_by(|a, b| a.module == b.module);
    imports
}

impl ModuleEnv {
    fn to_infer_scope(&self) -> InferScope {
        let traits = self
            .traits
            .iter()
            .map(|(name, entry)| (name.clone(), entry.def.clone()))
            .collect();
        let ops = self
            .ops
            .iter()
            .map(|(op, entry)| (op.clone(), entry.trait_name.clone()))
            .collect();
        let inherent = self
            .inherent_impls
            .iter()
            .map(|(target_name, entry)| (target_name.clone(), entry.methods.clone()))
            .collect();
        InferScope {
            type_names: self.types.keys().cloned().collect(),
            traits,
            ops,
            inherent_methods: inherent,
        }
    }

    /// Return all in-scope trait implementation dictionary names.
    pub fn all_dict_names(&self) -> HashSet<String> {
        self.impls
            .values()
            .map(|e| e.dict_name.clone())
            .chain(self.inherent_impls.values().map(|e| e.dict_name.clone()))
            .collect()
    }

    pub fn all_trait_impl_schemes(&self) -> HashMap<String, Scheme> {
        self.impls
            .values()
            .filter_map(|entry| {
                entry
                    .scheme
                    .clone()
                    .map(|scheme| (entry.dict_name.clone(), scheme))
            })
            .collect()
    }

    /// Look up a trait definition by name. Covers all in-scope traits: local, imported, prelude.
    pub fn trait_def(&self, name: &str) -> Option<&TraitDef> {
        self.traits.get(name).map(|e| &e.def)
    }

    /// Iterate over all in-scope trait definitions: local, imported, and prelude.
    pub fn all_trait_defs(&self) -> impl Iterator<Item = (&str, &TraitDef)> + '_ {
        self.traits.iter().map(|(k, v)| (k.as_str(), &v.def))
    }

    /// Iterate over all in-scope inherent methods by target type.
    pub fn all_inherent_methods(
        &self,
    ) -> impl Iterator<Item = (&str, &HashMap<String, InherentMethodScheme>)> + '_ {
        self.inherent_impls
            .iter()
            .map(|(target, entry)| (target.as_str(), &entry.methods))
    }

    pub fn exported_dict_names(&self) -> Vec<String> {
        self.dict_names_excluding_owner(PRELUDE_OWNER)
    }

    fn attach_inherent_method_schemes(
        &mut self,
        schemes: &HashMap<String, HashMap<String, InherentMethodScheme>>,
    ) {
        for (target, methods) in schemes {
            if let Some(entry) = self.inherent_impls.get_mut(target) {
                for (name, method) in methods {
                    if let Some(existing) = entry.methods.get_mut(name) {
                        existing.scheme = method.scheme.clone();
                        existing.has_receiver = method.has_receiver;
                    }
                }
            }
        }
    }

    fn attach_trait_impl_schemes(&mut self, env: &TypeEnv) {
        for entry in self.impls.values_mut() {
            if let Some(info) = env.get(&entry.dict_name) {
                entry.scheme = Some(info.scheme.clone());
            }
        }
    }

    fn dict_names_excluding_owner(&self, excluded_owner: &str) -> Vec<String> {
        let mut names: Vec<_> = self
            .impls
            .values()
            .filter(|entry| entry.owner != excluded_owner)
            .map(|entry| entry.dict_name.clone())
            .chain(
                self.inherent_impls
                    .values()
                    .filter(|entry| entry.owner != excluded_owner)
                    .map(|entry| entry.dict_name.clone()),
            )
            .collect();
        names.sort();
        names.dedup();
        names
    }
}

fn normalize_overlays(overlays: HashMap<PathBuf, String>) -> HashMap<PathBuf, String> {
    overlays
        .into_iter()
        .map(|(path, source)| (normalize_overlay_path(&path), source))
        .collect()
}

/// Normalizes a source-overlay path to the key used by `ModuleGraph`.
///
/// Existing files use their canonical filesystem path. Non-existing files keep a stable absolute
/// path so open editor buffers can be analyzed before they are saved to disk.
pub fn normalize_overlay_path(path: &Path) -> PathBuf {
    if let Ok(canonical) = fs::canonicalize(path) {
        return canonical;
    }
    if path.is_absolute() {
        path.to_path_buf()
    } else {
        std::env::current_dir()
            .map(|cwd| cwd.join(path))
            .unwrap_or_else(|_| path.to_path_buf())
    }
}

fn module_name(path: &Path) -> String {
    let mut hasher = DefaultHasher::new();
    path.hash(&mut hasher);
    format!("hern_mod_{:x}", hasher.finish())
}

fn diagnostic_source_for_module(graph: &ModuleGraph, name: &str) -> DiagnosticSource {
    graph
        .paths
        .get(name)
        .cloned()
        .map(DiagnosticSource::Path)
        .unwrap_or_else(|| DiagnosticSource::Module(name.to_string()))
}

fn resolve_imports_in_program(
    program: &mut Program,
    base_dir: &Path,
    graph: &mut ModuleGraph,
) -> Result<(), CompilerDiagnostic> {
    for stmt in &mut program.stmts {
        resolve_imports_in_stmt(stmt, base_dir, graph)?;
    }
    Ok(())
}

fn resolve_imports_in_program_recovering(
    program: &mut Program,
    base_dir: &Path,
    graph: &mut ModuleGraph,
    source: DiagnosticSource,
) -> Vec<CompilerDiagnostic> {
    let mut diagnostics = Vec::new();
    for stmt in &mut program.stmts {
        resolve_imports_in_stmt_recovering(stmt, base_dir, graph, source.clone(), &mut diagnostics);
    }
    diagnostics
}

fn resolve_imports_in_stmt(
    stmt: &mut Stmt,
    base_dir: &Path,
    graph: &mut ModuleGraph,
) -> Result<(), CompilerDiagnostic> {
    match stmt {
        Stmt::Let { value, .. } | Stmt::Expr(value) => {
            resolve_imports_in_expr(value, base_dir, graph)
        }
        Stmt::Fn { body, .. } | Stmt::Op { body, .. } => {
            resolve_imports_in_expr(body, base_dir, graph)
        }
        Stmt::Impl(id) => {
            for method in &mut id.methods {
                resolve_imports_in_expr(&mut method.body, base_dir, graph)?;
            }
            Ok(())
        }
        Stmt::InherentImpl(id) => {
            for method in &mut id.methods {
                resolve_imports_in_expr(&mut method.body, base_dir, graph)?;
            }
            Ok(())
        }
        Stmt::TestBlock { stmts, .. } => {
            for stmt in stmts {
                resolve_imports_in_stmt(stmt, base_dir, graph)?;
            }
            Ok(())
        }
        Stmt::RecBlock { stmts, .. } => {
            for stmt in stmts {
                resolve_imports_in_stmt(stmt, base_dir, graph)?;
            }
            Ok(())
        }
        Stmt::Macro(_)
        | Stmt::Type(_)
        | Stmt::TypeAlias { .. }
        | Stmt::Trait(_)
        | Stmt::Extern { .. } => Ok(()),
    }
}

fn resolve_imports_in_stmt_recovering(
    stmt: &mut Stmt,
    base_dir: &Path,
    graph: &mut ModuleGraph,
    source: DiagnosticSource,
    diagnostics: &mut Vec<CompilerDiagnostic>,
) {
    match stmt {
        Stmt::Let { value, .. } | Stmt::Expr(value) => {
            resolve_imports_in_expr_recovering(value, base_dir, graph, source, diagnostics);
        }
        Stmt::Fn { body, .. } | Stmt::Op { body, .. } => {
            resolve_imports_in_expr_recovering(body, base_dir, graph, source, diagnostics);
        }
        Stmt::Impl(id) => {
            for method in &mut id.methods {
                resolve_imports_in_expr_recovering(
                    &mut method.body,
                    base_dir,
                    graph,
                    source.clone(),
                    diagnostics,
                );
            }
        }
        Stmt::InherentImpl(id) => {
            for method in &mut id.methods {
                resolve_imports_in_expr_recovering(
                    &mut method.body,
                    base_dir,
                    graph,
                    source.clone(),
                    diagnostics,
                );
            }
        }
        Stmt::TestBlock { stmts, .. } => {
            for stmt in stmts {
                resolve_imports_in_stmt_recovering(
                    stmt,
                    base_dir,
                    graph,
                    source.clone(),
                    diagnostics,
                );
            }
        }
        Stmt::RecBlock { stmts, .. } => {
            for stmt in stmts {
                resolve_imports_in_stmt_recovering(
                    stmt,
                    base_dir,
                    graph,
                    source.clone(),
                    diagnostics,
                );
            }
        }
        Stmt::Macro(_)
        | Stmt::Type(_)
        | Stmt::TypeAlias { .. }
        | Stmt::Trait(_)
        | Stmt::Extern { .. } => {}
    }
}

fn resolve_imports_in_expr(
    expr: &mut Expr,
    base_dir: &Path,
    graph: &mut ModuleGraph,
) -> Result<(), CompilerDiagnostic> {
    match &mut expr.kind {
        ExprKind::Import(spec) => {
            let path = graph.resolve_import_path(base_dir, spec)?;
            *spec = graph.load_module(&path)?;
            Ok(())
        }
        ExprKind::Grouped(e)
        | ExprKind::Not(e)
        | ExprKind::Loop(e)
        | ExprKind::Break(Some(e))
        | ExprKind::Return(Some(e))
        | ExprKind::FieldAccess { expr: e, .. } => resolve_imports_in_expr(e, base_dir, graph),
        ExprKind::Neg { operand, .. } => resolve_imports_in_expr(operand, base_dir, graph),
        ExprKind::Index { receiver, key, .. } => {
            resolve_imports_in_expr(receiver, base_dir, graph)?;
            resolve_imports_in_expr(key, base_dir, graph)
        }
        ExprKind::AssociatedAccess { .. } => Ok(()),
        ExprKind::Assign { target, value }
        | ExprKind::Binary {
            lhs: target,
            rhs: value,
            ..
        } => {
            resolve_imports_in_expr(target, base_dir, graph)?;
            resolve_imports_in_expr(value, base_dir, graph)
        }
        ExprKind::Range { start, end, .. } => {
            if let Some(start) = start {
                resolve_imports_in_expr(start, base_dir, graph)?;
            }
            if let Some(end) = end {
                resolve_imports_in_expr(end, base_dir, graph)?;
            }
            Ok(())
        }
        ExprKind::Call { callee, args, .. } => {
            resolve_imports_in_expr(callee, base_dir, graph)?;
            for arg in args {
                resolve_imports_in_expr(arg, base_dir, graph)?;
            }
            Ok(())
        }
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
        } => {
            resolve_imports_in_expr(cond, base_dir, graph)?;
            resolve_imports_in_expr(then_branch, base_dir, graph)?;
            resolve_imports_in_expr(else_branch, base_dir, graph)
        }
        ExprKind::Match { scrutinee, arms } => {
            resolve_imports_in_expr(scrutinee, base_dir, graph)?;
            for (_, body) in arms {
                resolve_imports_in_expr(body, base_dir, graph)?;
            }
            Ok(())
        }
        ExprKind::Block { stmts, final_expr } => {
            for stmt in stmts {
                resolve_imports_in_stmt(stmt, base_dir, graph)?;
            }
            if let Some(expr) = final_expr {
                resolve_imports_in_expr(expr, base_dir, graph)?;
            }
            Ok(())
        }
        ExprKind::Tuple(items) => {
            for item in items {
                resolve_imports_in_expr(item, base_dir, graph)?;
            }
            Ok(())
        }
        ExprKind::Array(entries) => {
            for entry in entries {
                resolve_imports_in_expr(entry.expr_mut(), base_dir, graph)?;
            }
            Ok(())
        }
        ExprKind::Record(entries) => {
            for entry in entries {
                resolve_imports_in_expr(entry.expr_mut(), base_dir, graph)?;
            }
            Ok(())
        }
        ExprKind::Lambda { body, .. } => resolve_imports_in_expr(body, base_dir, graph),
        ExprKind::For { iterable, body, .. } => {
            resolve_imports_in_expr(iterable, base_dir, graph)?;
            resolve_imports_in_expr(body, base_dir, graph)
        }
        ExprKind::Break(None)
        | ExprKind::Return(None)
        | ExprKind::Continue
        | ExprKind::Number(_)
        | ExprKind::StringLit(_)
        | ExprKind::Bool(_)
        | ExprKind::SyntaxQuote(_)
        | ExprKind::MacroCall { .. }
        | ExprKind::Ident(_)
        | ExprKind::Unit => Ok(()),
    }
}

fn resolve_imports_in_expr_recovering(
    expr: &mut Expr,
    base_dir: &Path,
    graph: &mut ModuleGraph,
    source: DiagnosticSource,
    diagnostics: &mut Vec<CompilerDiagnostic>,
) {
    match &mut expr.kind {
        ExprKind::Import(spec) => {
            let path = match graph.resolve_import_path(base_dir, spec) {
                Ok(path) => path,
                Err(err) => {
                    diagnostics.push(err.with_source_if_absent(source));
                    return;
                }
            };
            let (name, module_diagnostics) = graph.load_module_recovering(&path);
            *spec = name;
            diagnostics.extend(module_diagnostics);
        }
        ExprKind::Grouped(e)
        | ExprKind::Not(e)
        | ExprKind::Loop(e)
        | ExprKind::Break(Some(e))
        | ExprKind::Return(Some(e))
        | ExprKind::FieldAccess { expr: e, .. } => {
            resolve_imports_in_expr_recovering(e, base_dir, graph, source, diagnostics);
        }
        ExprKind::Neg { operand, .. } => {
            resolve_imports_in_expr_recovering(operand, base_dir, graph, source, diagnostics);
        }
        ExprKind::Index { receiver, key, .. } => {
            resolve_imports_in_expr_recovering(
                receiver,
                base_dir,
                graph,
                source.clone(),
                diagnostics,
            );
            resolve_imports_in_expr_recovering(key, base_dir, graph, source, diagnostics);
        }
        ExprKind::AssociatedAccess { .. } => {}
        ExprKind::Assign { target, value }
        | ExprKind::Binary {
            lhs: target,
            rhs: value,
            ..
        } => {
            resolve_imports_in_expr_recovering(
                target,
                base_dir,
                graph,
                source.clone(),
                diagnostics,
            );
            resolve_imports_in_expr_recovering(value, base_dir, graph, source, diagnostics);
        }
        ExprKind::Range { start, end, .. } => {
            if let Some(start) = start {
                resolve_imports_in_expr_recovering(
                    start,
                    base_dir,
                    graph,
                    source.clone(),
                    diagnostics,
                );
            }
            if let Some(end) = end {
                resolve_imports_in_expr_recovering(end, base_dir, graph, source, diagnostics);
            }
        }
        ExprKind::Call { callee, args, .. } => {
            resolve_imports_in_expr_recovering(
                callee,
                base_dir,
                graph,
                source.clone(),
                diagnostics,
            );
            for arg in args {
                resolve_imports_in_expr_recovering(
                    arg,
                    base_dir,
                    graph,
                    source.clone(),
                    diagnostics,
                );
            }
        }
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
        } => {
            resolve_imports_in_expr_recovering(cond, base_dir, graph, source.clone(), diagnostics);
            resolve_imports_in_expr_recovering(
                then_branch,
                base_dir,
                graph,
                source.clone(),
                diagnostics,
            );
            resolve_imports_in_expr_recovering(else_branch, base_dir, graph, source, diagnostics);
        }
        ExprKind::Match { scrutinee, arms } => {
            resolve_imports_in_expr_recovering(
                scrutinee,
                base_dir,
                graph,
                source.clone(),
                diagnostics,
            );
            for (_, body) in arms {
                resolve_imports_in_expr_recovering(
                    body,
                    base_dir,
                    graph,
                    source.clone(),
                    diagnostics,
                );
            }
        }
        ExprKind::Block { stmts, final_expr } => {
            for stmt in stmts {
                resolve_imports_in_stmt_recovering(
                    stmt,
                    base_dir,
                    graph,
                    source.clone(),
                    diagnostics,
                );
            }
            if let Some(expr) = final_expr {
                resolve_imports_in_expr_recovering(expr, base_dir, graph, source, diagnostics);
            }
        }
        ExprKind::Tuple(items) => {
            for item in items {
                resolve_imports_in_expr_recovering(
                    item,
                    base_dir,
                    graph,
                    source.clone(),
                    diagnostics,
                );
            }
        }
        ExprKind::Array(entries) => {
            for entry in entries {
                resolve_imports_in_expr_recovering(
                    entry.expr_mut(),
                    base_dir,
                    graph,
                    source.clone(),
                    diagnostics,
                );
            }
        }
        ExprKind::Record(entries) => {
            for entry in entries {
                resolve_imports_in_expr_recovering(
                    entry.expr_mut(),
                    base_dir,
                    graph,
                    source.clone(),
                    diagnostics,
                );
            }
        }
        ExprKind::Lambda { body, .. } => {
            resolve_imports_in_expr_recovering(body, base_dir, graph, source, diagnostics);
        }
        ExprKind::For { iterable, body, .. } => {
            resolve_imports_in_expr_recovering(
                iterable,
                base_dir,
                graph,
                source.clone(),
                diagnostics,
            );
            resolve_imports_in_expr_recovering(body, base_dir, graph, source, diagnostics);
        }
        ExprKind::Break(None)
        | ExprKind::Return(None)
        | ExprKind::Continue
        | ExprKind::Number(_)
        | ExprKind::StringLit(_)
        | ExprKind::Bool(_)
        | ExprKind::SyntaxQuote(_)
        | ExprKind::MacroCall { .. }
        | ExprKind::Ident(_)
        | ExprKind::Unit => {}
    }
}

fn build_module_env(
    graph: &ModuleGraph,
    module_envs: &HashMap<String, ModuleEnv>,
    prelude_env: &ModuleEnv,
    name: &str,
) -> Result<ModuleEnv, CompilerDiagnostic> {
    let program = graph.modules.get(name).ok_or_else(|| {
        CompilerDiagnostic::error_in(
            diagnostic_source_for_module(graph, name),
            None,
            format!("internal error: loaded module `{}` missing", name),
        )
    })?;
    let mut env = prelude_env.clone();
    for import in collect_imports_with_spans(program) {
        let imported_env = module_envs.get(&import.module).ok_or_else(|| {
            CompilerDiagnostic::error_in(
                diagnostic_source_for_module(graph, name),
                None,
                format!(
                    "internal error: imported module `{}` not inferred yet",
                    import.module
                ),
            )
        })?;
        merge_module_env(&mut env, imported_env, Some(import.span))?;
    }
    add_own_module_env(&mut env, program, name)
        .map_err(|err| err.with_source_if_absent(diagnostic_source_for_module(graph, name)))?;
    Ok(env)
}

fn module_env_from_program(
    program: &Program,
    owner: &str,
) -> Result<ModuleEnv, CompilerDiagnostic> {
    let mut env = ModuleEnv::default();
    add_own_module_env(&mut env, program, owner)?;
    Ok(env)
}

fn merge_module_env(
    dst: &mut ModuleEnv,
    src: &ModuleEnv,
    import_span: Option<SourceSpan>,
) -> Result<(), CompilerDiagnostic> {
    for (name, entry) in &src.types {
        add_type_env(dst, name.clone(), entry.clone(), true, import_span)?;
    }
    for (name, entry) in &src.traits {
        add_trait_env(dst, name.clone(), entry.clone(), true, import_span)?;
    }
    for (op, entry) in &src.ops {
        add_op_env(dst, op.clone(), entry.clone(), true)?;
    }
    for (key, entry) in &src.impls {
        add_impl_env(dst, key.clone(), entry.clone(), true)?;
    }
    for (target, entry) in &src.inherent_impls {
        add_inherent_impl_env(dst, target.clone(), entry.clone(), true)?;
    }
    Ok(())
}

fn add_own_module_env(
    env: &mut ModuleEnv,
    program: &Program,
    owner: &str,
) -> Result<(), CompilerDiagnostic> {
    for stmt in program.stmts.iter() {
        match stmt {
            Stmt::Type(td) => {
                add_type_env(
                    env,
                    td.name.clone(),
                    EnvType {
                        owner: owner.to_string(),
                    },
                    false,
                    Some(td.name_span),
                )
                .map_err(|err| err.with_span_if_absent(td.name_span))?;
            }
            Stmt::TypeAlias {
                name, name_span, ..
            } => {
                add_type_env(
                    env,
                    name.clone(),
                    EnvType {
                        owner: owner.to_string(),
                    },
                    false,
                    Some(*name_span),
                )
                .map_err(|err| err.with_span_if_absent(*name_span))?;
            }
            Stmt::Trait(td) => {
                add_trait_env(
                    env,
                    td.name.clone(),
                    EnvTrait {
                        def: td.clone(),
                        owner: owner.to_string(),
                    },
                    false,
                    Some(td.name_span),
                )
                .map_err(|err| err.with_span_if_absent(td.name_span))?;
                for method in &td.methods {
                    if method.fixity.is_some() {
                        add_op_env(
                            env,
                            method.name.clone(),
                            EnvOp {
                                trait_name: td.name.clone(),
                                owner: owner.to_string(),
                            },
                            false,
                        )
                        .map_err(|err| err.with_span_if_absent(method.span))?;
                    }
                }
            }
            Stmt::Impl(id) => {
                let indexes = if let Some(entry) = env.traits.get(&id.trait_name) {
                    // Keep malformed impls out of the early module-env index.
                    // The inference pass owns the user-facing diagnostic; this
                    // pass only registers impls that are safe to name/import.
                    if id.trait_args.len() != entry.def.params.len() {
                        continue;
                    }
                    if let Some(fundep) = entry.def.fundeps.first() {
                        if id.fundep_arrow_index != Some(fundep.determinants.len()) {
                            continue;
                        }
                    } else if id.used_fundep_arrow {
                        continue;
                    }
                    trait_dict_indexes(&entry.def)
                } else {
                    (0..id.trait_args.len()).collect()
                };
                let arg_keys = indexes
                    .iter()
                    .map(|index| trait_impl_arg_keys_from_ast(&[id.trait_args[*index].clone()]))
                    .collect::<Result<Vec<_>, _>>()
                    .map(|keys| keys.into_iter().flatten().collect::<Vec<_>>())
                    .map_err(|err| CompilerDiagnostic::error(Some(id.span), err.to_string()))?;
                let key = ImplKey {
                    trait_name: id.trait_name.clone(),
                    args: arg_keys.clone(),
                };
                add_impl_env(
                    env,
                    key,
                    EnvImpl {
                        dict_name: trait_impl_dict_name_for_indexes(
                            &id.trait_name,
                            &id.trait_args,
                            &indexes,
                        )
                        .map_err(|err| CompilerDiagnostic::error(Some(id.span), err.to_string()))?,
                        scheme: None,
                        owner: owner.to_string(),
                    },
                    false,
                )
                .map_err(|err| err.with_span_if_absent(id.span))?;
            }
            Stmt::InherentImpl(id) => {
                let target = module_inherent_impl_target_key(&id.target)
                    .map_err(|err| CompilerDiagnostic::error(Some(id.span), err.to_string()))?;
                add_inherent_impl_env(
                    env,
                    target.clone(),
                    EnvInherentImpl {
                        methods: id
                            .methods
                            .iter()
                            .map(|method| {
                                (
                                    method.name.clone(),
                                    InherentMethodScheme {
                                        scheme: Scheme::mono(Ty::Unit),
                                        has_receiver: method
                                            .params
                                            .first()
                                            .is_some_and(is_self_param),
                                    },
                                )
                            })
                            .collect(),
                        dict_name: format!("__impl__{}", target),
                        owner: owner.to_string(),
                    },
                    false,
                )
                .map_err(|err| err.with_span_if_absent(id.span))?;
            }
            _ => {}
        }
    }
    Ok(())
}

fn module_inherent_impl_target_key(
    target: &crate::ast::Type,
) -> Result<String, crate::types::error::TypeError> {
    match target {
        crate::ast::Type::Ident(name) => Ok(name.clone()),
        crate::ast::Type::App(_, args)
            if args
                .iter()
                .all(|arg| matches!(arg, crate::ast::Type::Var(_))) =>
        {
            Ok(module_inherent_impl_generic_target_name(target))
        }
        _ => exact_impl_target_key_from_ast(target),
    }
}

fn module_inherent_impl_generic_target_name(target: &crate::ast::Type) -> String {
    match target {
        crate::ast::Type::Ident(name) => name.clone(),
        crate::ast::Type::App(con, _) => module_inherent_impl_generic_target_name(con),
        _ => "Unknown".to_string(),
    }
}

fn add_type_env(
    env: &mut ModuleEnv,
    name: String,
    entry: EnvType,
    _allow_same_owner: bool,
    span: Option<SourceSpan>,
) -> Result<(), CompilerDiagnostic> {
    if let Some(existing) = env.traits.get(&name) {
        return Err(CompilerDiagnostic::error(
            span,
            type_trait_collision_message(&name, "type", "trait", &existing.owner),
        ));
    }
    env.types.entry(name).or_insert(entry);
    Ok(())
}

fn add_trait_env(
    env: &mut ModuleEnv,
    name: String,
    entry: EnvTrait,
    allow_same_owner: bool,
    span: Option<SourceSpan>,
) -> Result<(), CompilerDiagnostic> {
    if let Some(existing) = env.types.get(&name) {
        return Err(CompilerDiagnostic::error(
            span,
            type_trait_collision_message(&name, "trait", "type", &existing.owner),
        ));
    }
    if let Some(existing) = env.traits.get(&name)
        && (!allow_same_owner || existing.owner != entry.owner)
    {
        return Err(CompilerDiagnostic::error(
            None,
            format!("trait `{}` is defined in multiple modules", name),
        ));
    }
    env.traits.entry(name).or_insert(entry);
    Ok(())
}

fn type_trait_collision_message(
    name: &str,
    new_kind: &str,
    existing_kind: &str,
    existing_owner: &str,
) -> String {
    format!(
        "{} `{}` collides with {} `{}` from {}",
        new_kind,
        name,
        existing_kind,
        name,
        owner_for_diagnostic(existing_owner)
    )
}

fn owner_for_diagnostic(owner: &str) -> String {
    match owner {
        PRELUDE_OWNER => "prelude".to_string(),
        other => format!("module `{}`", other),
    }
}

fn add_op_env(
    env: &mut ModuleEnv,
    op: String,
    entry: EnvOp,
    allow_same_owner: bool,
) -> Result<(), CompilerDiagnostic> {
    if let Some(existing) = env.ops.get(&op)
        && ((!allow_same_owner || existing.owner != entry.owner)
            || existing.trait_name != entry.trait_name)
    {
        return Err(CompilerDiagnostic::error(
            None,
            format!("operator `{}` is defined in multiple traits", op),
        ));
    }
    env.ops.entry(op).or_insert(entry);
    Ok(())
}

fn add_impl_env(
    env: &mut ModuleEnv,
    key: ImplKey,
    entry: EnvImpl,
    allow_same_owner: bool,
) -> Result<(), CompilerDiagnostic> {
    if let Some(existing) = env.impls.get(&key)
        && (!allow_same_owner || existing.owner != entry.owner)
    {
        return Err(CompilerDiagnostic::error(
            None,
            format!(
                "impl {} for {} is defined in multiple modules",
                key.trait_name,
                key.args.join(", ")
            ),
        ));
    }
    env.impls.entry(key).or_insert(entry);
    Ok(())
}

fn add_inherent_impl_env(
    env: &mut ModuleEnv,
    target: String,
    entry: EnvInherentImpl,
    allow_same_owner: bool,
) -> Result<(), CompilerDiagnostic> {
    if let Some(existing) = env.inherent_impls.get_mut(&target) {
        if !allow_same_owner || existing.owner != entry.owner {
            let duplicate = entry
                .methods
                .keys()
                .find(|method| existing.methods.contains_key(*method))
                .cloned();
            if let Some(method) = duplicate {
                return Err(CompilerDiagnostic::error(
                    None,
                    format!(
                        "method `{}` is already defined for inherent impl target `{}`",
                        method, target
                    ),
                ));
            }
        }
        existing.methods.extend(entry.methods);
        return Ok(());
    }
    env.inherent_impls.insert(target, entry);
    Ok(())
}

fn is_self_param(param: &Param) -> bool {
    matches!(&param.pat, Pattern::Variable(name, _) if name == "self")
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::{SystemTime, UNIX_EPOCH};

    #[test]
    fn module_lookup_by_path_returns_loaded_program() {
        let test_dir = std::env::temp_dir().join(format!(
            "hern-module-lookup-{}-{}",
            std::process::id(),
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .expect("system time should be after epoch")
                .as_nanos()
        ));
        fs::create_dir_all(&test_dir).expect("temp test directory should be created");

        let dep_path = test_dir.join("dep.hern");
        let entry_path = test_dir.join("main.hern");
        fs::write(&dep_path, "fn value() { 1 }\n#{ value: value }\n")
            .expect("dep module should be written");
        fs::write(&entry_path, "let dep = import \"dep\";\ndep.value()\n")
            .expect("entry module should be written");

        let (graph, entry_name) =
            ModuleGraph::load_entry(&entry_path).expect("module graph should load");
        assert_eq!(
            graph.module_name_for_path(&entry_path),
            Some(entry_name.as_str())
        );

        let (lookup_name, program) = graph
            .module_for_path(&entry_path)
            .expect("entry module should be found by path");
        assert_eq!(lookup_name, entry_name);
        assert!(!program.stmts.is_empty());

        let dep_name = graph
            .module_name_for_path(&dep_path)
            .expect("imported module should be found by path");
        assert!(graph.module(dep_name).is_some());
        assert!(graph.module_path(dep_name).is_some());
    }

    #[test]
    fn load_entry_uses_overlay_for_nonexistent_entry_and_import() {
        let test_dir = std::env::temp_dir().join(format!(
            "hern-overlay-entry-{}-{}",
            std::process::id(),
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .expect("system time should be after epoch")
                .as_nanos()
        ));
        fs::create_dir_all(&test_dir).expect("temp test directory should be created");

        let entry_path = test_dir.join("main.hern");
        let dep_path = test_dir.join("dep.hern");
        let overlays = HashMap::from([
            (
                entry_path.clone(),
                "let dep = import \"dep\";\ndep.value\n".to_string(),
            ),
            (dep_path.clone(), "#{ value: 1 }\n".to_string()),
        ]);

        let (graph, entry_name) = ModuleGraph::load_entry_with_overlays(&entry_path, overlays)
            .expect("graph should load from unsaved overlays");

        assert!(graph.module(&entry_name).is_some());
        assert!(graph.module_name_for_path(&dep_path).is_some());
        assert!(
            !entry_path.exists(),
            "test must exercise non-existing entry overlays"
        );
        assert!(
            !dep_path.exists(),
            "test must exercise non-existing imported overlays"
        );
    }

    #[test]
    fn parse_file_recovering_reports_multiple_file_diagnostics() {
        let test_dir = std::env::temp_dir().join(format!(
            "hern-file-recovery-{}-{}",
            std::process::id(),
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .expect("system time should be after epoch")
                .as_nanos()
        ));
        fs::create_dir_all(&test_dir).expect("temp test directory should be created");

        let path = test_dir.join("bad.hern");
        fs::write(&path, "let a = ;\nlet b = ;\n").expect("bad module should be written");

        let graph = ModuleGraph::new().expect("module graph should initialize");
        let output = parse_file_recovering(&path, &graph.prelude)
            .expect("recovering parser should read and lex the file");
        let diagnostics = output
            .into_result()
            .expect_err("invalid file should return diagnostics");

        assert_eq!(diagnostics.len(), 2);
        for diagnostic in diagnostics {
            assert_eq!(
                diagnostic.source,
                Some(DiagnosticSource::Path(path.clone()))
            );
            assert!(diagnostic.span.is_some());
        }
    }

    #[test]
    fn parse_file_recovering_expands_derives() {
        let test_dir = std::env::temp_dir().join(format!(
            "hern-file-recovery-derives-{}-{}",
            std::process::id(),
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .expect("system time should be after epoch")
                .as_nanos()
        ));
        fs::create_dir_all(&test_dir).expect("temp test directory should be created");

        let path = test_dir.join("main.hern");
        fs::write(&path, "#[derive(Eq)]\ntype Box('a) = Box('a)\n")
            .expect("module should be written");

        let graph = ModuleGraph::new().expect("module graph should initialize");
        let output = parse_file_recovering(&path, &graph.prelude)
            .expect("recovering parser should read and lex the file");
        let program = output
            .into_result()
            .expect("valid file should return a parsed program");

        assert!(program.stmts.iter().any(|stmt| {
            matches!(
                stmt,
                Stmt::Impl(impl_def)
                    if impl_def.generated_by.is_some() && impl_def.trait_name == "Eq"
            )
        }));
    }

    #[test]
    fn load_entry_recovering_reports_imported_parse_diagnostics() {
        let test_dir = std::env::temp_dir().join(format!(
            "hern-graph-recovery-{}-{}",
            std::process::id(),
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .expect("system time should be after epoch")
                .as_nanos()
        ));
        fs::create_dir_all(&test_dir).expect("temp test directory should be created");

        let dep_path = test_dir.join("dep.hern");
        let entry_path = test_dir.join("main.hern");
        fs::write(&dep_path, "let a = ;\nlet b = ;\n").expect("dep module should be written");
        fs::write(&entry_path, "let dep = import \"dep\";\n")
            .expect("entry module should be written");

        let output = ModuleGraph::load_entry_recovering(&entry_path)
            .expect("recovering graph load should initialize");
        let dep_path = fs::canonicalize(dep_path).expect("dep path should canonicalize");
        let diagnostics = match output.into_result() {
            Ok(_) => panic!("imported parse errors should prevent graph success"),
            Err(diagnostics) => diagnostics,
        };

        assert_eq!(diagnostics.len(), 2);
        for diagnostic in diagnostics {
            assert_eq!(
                diagnostic.source,
                Some(DiagnosticSource::Path(dep_path.clone()))
            );
            assert!(diagnostic.span.is_some());
        }
    }

    #[test]
    fn load_module_cleans_loading_set_after_parse_error() {
        let test_dir = std::env::temp_dir().join(format!(
            "hern-load-cleanup-{}-{}",
            std::process::id(),
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .expect("system time should be after epoch")
                .as_nanos()
        ));
        fs::create_dir_all(&test_dir).expect("temp test directory should be created");

        let path = test_dir.join("module.hern");
        fs::write(&path, "let value = ;\n").expect("bad module should be written");
        let mut graph = ModuleGraph::new().expect("module graph should initialize");

        graph
            .load_module(&path)
            .expect_err("invalid module should fail to load");
        fs::write(&path, "let value = 1;\n").expect("fixed module should be written");

        graph
            .load_module(&path)
            .expect("fixed module should load without false circular import");
    }

    #[test]
    fn recovering_load_module_cleans_loading_set_after_lex_error() {
        let test_dir = std::env::temp_dir().join(format!(
            "hern-recovering-load-cleanup-{}-{}",
            std::process::id(),
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .expect("system time should be after epoch")
                .as_nanos()
        ));
        fs::create_dir_all(&test_dir).expect("temp test directory should be created");

        let path = test_dir.join("module.hern");
        fs::write(&path, "let value = \"unterminated;\n").expect("bad module should be written");
        let mut graph = ModuleGraph::new().expect("module graph should initialize");

        let (_, diagnostics) = graph.load_module_recovering(&path);
        assert_eq!(diagnostics.len(), 1);

        fs::write(&path, "let value = 1;\n").expect("fixed module should be written");
        let (_, diagnostics) = graph.load_module_recovering(&path);

        assert!(diagnostics.is_empty());
    }
}
