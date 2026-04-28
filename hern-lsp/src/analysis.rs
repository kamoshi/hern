#![allow(clippy::mutable_key_type)]
use hern_core::analysis::{
    CompilerDiagnostic, DiagnosticSeverity as CoreDiagnosticSeverity, DiagnosticSource,
    PreludeAnalysis, analyze_prelude, hover_at,
};
use hern_core::ast::{
    Expr, ExprKind, ImplMethod, Pattern, Program, SourcePosition, SourceSpan, Stmt,
};
use hern_core::module::{GraphInference, ModuleGraph, infer_graph};
use hern_core::pipeline::parse_source_recovering;
use hern_core::source_index::{
    CompletionCandidateKind, Definition, DefinitionKind, ImportMemberReference, index_program,
};
use hern_core::types::infer::{TypeEnv, VariantEnv};
use hern_core::types::{
    Scheme, TraitConstraint, Ty, TyVar, display_ty_with_var_names, free_type_vars_in_display_order,
    type_var_name,
};
use hern_core::workspace::{WorkspaceInputs, analyze_workspace};
use lsp_types::{
    CompletionItem, CompletionItemKind, CompletionItemLabelDetails, CompletionTextEdit, Diagnostic,
    DiagnosticSeverity, Hover, HoverContents, Location, MarkupContent, MarkupKind, Position, Range,
    TextEdit, Uri, WorkspaceEdit,
};
use std::collections::{HashMap, HashSet};
use std::fs;
use std::path::{Path, PathBuf};
use std::str::FromStr;

pub(crate) type DiagnosticsByUri = HashMap<Uri, Vec<Diagnostic>>;

pub(crate) struct ServerState {
    pub(crate) documents: HashMap<Uri, String>,
    pub(crate) document_versions: HashMap<Uri, i32>,
    pub(crate) diagnostics_by_entry: HashMap<Uri, DiagnosticsByUri>,
    entry_dependencies: HashMap<Uri, HashSet<Uri>>,
    cached_analyses: HashMap<Uri, CachedAnalysis>,
    /// URIs that were explicitly opened by the client (via didOpen) and are treated as
    /// entry-point documents. A document absent from this set but present in another
    /// entry's `entry_dependencies` is dependency-only and should not get its own
    /// entry-level diagnostic lifecycle.
    open_entry_uris: HashSet<Uri>,
    prelude: PreludeAnalysis,
    /// Whether the client advertised `markdown` in its hover `contentFormat` capability.
    /// When false, plain text is used instead of Markdown fenced blocks.
    pub(crate) supports_markdown_hover: bool,
}

#[derive(Clone)]
struct CachedAnalysis {
    document_versions: HashMap<Uri, i32>,
    graph: ModuleGraph,
    inference: GraphInference,
}

impl ServerState {
    pub(crate) fn new() -> Result<Self, CompilerDiagnostic> {
        Ok(Self {
            documents: HashMap::new(),
            document_versions: HashMap::new(),
            diagnostics_by_entry: HashMap::new(),
            entry_dependencies: HashMap::new(),
            cached_analyses: HashMap::new(),
            open_entry_uris: HashSet::new(),
            prelude: analyze_prelude()?,
            supports_markdown_hover: true,
        })
    }

    /// Marks `uri` as a client-opened entry document. Call this when a didOpen notification
    /// arrives. Does nothing if the URI is already marked.
    pub(crate) fn mark_open_entry(&mut self, uri: Uri) {
        self.open_entry_uris.insert(uri);
    }

    /// Unmarks `uri` as a client-opened entry. Call this when a didClose notification
    /// arrives before removing the document overlay.
    pub(crate) fn unmark_open_entry(&mut self, uri: &Uri) {
        self.open_entry_uris.remove(uri);
    }

    /// Returns `true` if `uri` was explicitly opened by the client and is being tracked
    /// as an entry-point document.
    pub(crate) fn is_open_entry(&self, uri: &Uri) -> bool {
        self.open_entry_uris.contains(uri)
    }

    pub(crate) fn set_document(&mut self, uri: Uri, text: String, version: i32) {
        self.documents.insert(uri.clone(), text);
        self.document_versions.insert(uri.clone(), version);
        self.invalidate_cached_analyses_for_document(&uri);
    }

    pub(crate) fn remove_document(&mut self, uri: &Uri) {
        self.documents.remove(uri);
        self.document_versions.remove(uri);
        self.invalidate_cached_analyses_for_document(uri);
    }

    pub(crate) fn entries_affected_by_document(&self, uri: &Uri) -> HashSet<Uri> {
        // Only treat `uri` itself as an affected entry if the client opened it as one.
        // A document that appears only as a dependency of another entry should not be
        // re-analysed independently when it changes — the owning entries handle that.
        let mut entries = if self.open_entry_uris.contains(uri) {
            HashSet::from([uri.clone()])
        } else {
            HashSet::new()
        };
        entries.extend(
            self.entry_dependencies
                .iter()
                .filter(|(_, dependencies)| dependencies.contains(uri))
                .map(|(entry, _)| entry.clone()),
        );
        entries
    }

    fn invalidate_cached_analyses_for_document(&mut self, uri: &Uri) {
        for entry in self.entries_affected_by_document(uri) {
            self.cached_analyses.remove(&entry);
        }
    }

    fn update_entry_dependencies(
        &mut self,
        entry_uri: &Uri,
        graph: Option<&ModuleGraph>,
    ) -> HashSet<Uri> {
        let dependencies = graph
            .map(graph_module_uris)
            .unwrap_or_else(|| HashSet::from([entry_uri.clone()]));
        self.entry_dependencies
            .insert(entry_uri.clone(), dependencies.clone());
        dependencies
    }

    pub(crate) fn remove_entry_tracking(&mut self, entry_uri: &Uri) {
        self.entry_dependencies.remove(entry_uri);
        self.cached_analyses.remove(entry_uri);
    }
}

pub(crate) fn diagnostics_for_document(
    state: &mut ServerState,
    entry_uri: &Uri,
) -> DiagnosticsByUri {
    if let Some(source) = state.documents.get(entry_uri) {
        match parse_source_recovering(source) {
            Ok(parsed) if !parsed.diagnostics.is_empty() => {
                state.update_entry_dependencies(entry_uri, None);
                return diagnostics_from_compiler_diagnostics(entry_uri, parsed.diagnostics);
            }
            Ok(_) => {}
            Err(diagnostic) => {
                state.update_entry_dependencies(entry_uri, None);
                return diagnostics_from_compiler_diagnostics(entry_uri, vec![diagnostic]);
            }
        }
    }

    let path = match uri_to_path(entry_uri) {
        Some(path) => path,
        None => {
            return diagnostics_from_compiler_diagnostics(
                entry_uri,
                vec![CompilerDiagnostic::error(
                    None,
                    format!("unsupported document URI: {}", entry_uri.as_str()),
                )],
            );
        }
    };
    let analysis = analyze_workspace(WorkspaceInputs {
        entry: path,
        overlays: document_overlays(state),
        prelude: Some(state.prelude.program.clone()),
    });
    let dependencies = state.update_entry_dependencies(entry_uri, analysis.graph.as_ref());
    if analysis.diagnostics.is_empty()
        && let (Some(graph), Some(inference)) = (analysis.graph, analysis.inference)
    {
        state.cached_analyses.insert(
            entry_uri.clone(),
            CachedAnalysis {
                document_versions: document_versions_for_uris(state, &dependencies),
                graph,
                inference,
            },
        );
    }
    diagnostics_from_compiler_diagnostics(entry_uri, analysis.diagnostics)
}

pub(crate) fn combined_diagnostics_for_uri(state: &ServerState, uri: &Uri) -> Vec<Diagnostic> {
    let mut diagnostics = Vec::new();
    let mut seen = HashSet::new();
    for by_uri in state.diagnostics_by_entry.values() {
        if let Some(items) = by_uri.get(uri) {
            for diagnostic in items {
                if seen.insert(diagnostic_identity(diagnostic)) {
                    diagnostics.push(diagnostic.clone());
                }
            }
        }
    }
    diagnostics
}

pub(crate) fn hover(state: &ServerState, uri: Uri, position: Position) -> Option<Hover> {
    let path = uri_to_path(&uri)?;
    let fallback;
    let (graph, inference) = if let Some(analysis) = cached_analysis(state, &uri) {
        (&analysis.graph, &analysis.inference)
    } else {
        let analysis = analyze_workspace(WorkspaceInputs {
            entry: path.clone(),
            overlays: document_overlays(state),
            prelude: Some(state.prelude.program.clone()),
        });
        fallback = WorkspaceAnalysis {
            graph: analysis.graph?,
            inference: analysis.inference?,
        };
        (&fallback.graph, &fallback.inference)
    };
    let (module_name, program) = graph.module_for_path(&path)?;
    let expr_types = inference.expr_types_for_module(module_name)?;
    let symbol_types = inference.symbol_types_for_module(module_name)?;
    let position = SourcePosition {
        line: position.line as usize + 1,
        col: position.character as usize + 1,
    };
    let markdown = state.supports_markdown_hover;
    if let Some(contents) = symbol_hover(graph, inference, module_name, program, position) {
        return Some(type_hover(contents, markdown));
    }
    let info = hover_at(program, expr_types, symbol_types, position)?;
    Some(type_hover(ty_to_display_string(&info.ty), markdown))
}

/// Wrap a type string for display in a hover response.
///
/// When `markdown` is true (client advertised markdown hover support), the type is
/// wrapped in a fenced `hern` code block so editors can syntax-highlight it.
/// When false, a plain-text response is returned for compatibility with older clients.
fn type_hover(ty: String, markdown: bool) -> Hover {
    let contents = if markdown {
        HoverContents::Markup(MarkupContent {
            kind: MarkupKind::Markdown,
            value: format!("```hern\n{ty}\n```"),
        })
    } else {
        HoverContents::Markup(MarkupContent {
            kind: MarkupKind::PlainText,
            value: ty,
        })
    };
    Hover {
        contents,
        range: None,
    }
}

fn symbol_hover(
    graph: &ModuleGraph,
    inference: &GraphInference,
    module_name: &str,
    program: &Program,
    position: SourcePosition,
) -> Option<String> {
    let index = index_program(program);
    if let Some(reference) = index.import_member_reference_at(position) {
        return imported_member_hover_text(graph, inference, reference);
    }

    let definition = index.definition_at(position)?;
    definition_hover_text(
        definition,
        inference.env_for_module(module_name),
        inference.expr_types_for_module(module_name),
        inference.binding_types_for_module(module_name),
        inference.definition_schemes_for_module(module_name),
        inference.variant_env_for_module(module_name),
        program,
    )
}

/// Display a bare `Ty` with normalized type variable names.
///
/// Unlike `ty.to_string()`, this wraps the type in a `Scheme` so that internal
/// type variable IDs (e.g. `'70`) are renamed to human-readable names (`'a`, `'b`, …).
fn ty_to_display_string(ty: &Ty) -> String {
    let vars = free_type_vars_in_display_order(ty);
    let constraints = match ty {
        Ty::Qualified(constraints, _) => constraints.clone(),
        _ => vec![],
    };
    scheme_to_display_string(
        &Scheme {
            vars,
            constraints,
            ty: ty.clone(),
        },
        true,
    )
}

fn completion_ty_to_display_string(ty: &Ty) -> String {
    let vars = free_type_vars_in_display_order(ty);
    let constraints = match ty {
        Ty::Qualified(constraints, _) => constraints.clone(),
        _ => vec![],
    };
    scheme_to_display_string(
        &Scheme {
            vars,
            constraints,
            ty: ty.clone(),
        },
        false,
    )
}

fn hover_scheme_to_string(scheme: &Scheme) -> String {
    scheme_to_display_string(scheme, true)
}

fn completion_scheme_to_string(scheme: &Scheme) -> String {
    scheme_to_display_string(scheme, false)
}

fn scheme_to_display_string(scheme: &Scheme, include_constraints: bool) -> String {
    let names = type_var_names(scheme);
    let mut out = display_ty_body_for_lsp(&scheme.ty, &names);
    if include_constraints {
        let constraints = constraints_by_var(scheme, &names);
        if !constraints.is_empty() {
            out.push_str("\n\nConstraints:");
            for (name, traits) in constraints {
                out.push_str(&format!("\n- '{}: {}", name, traits.join(" + ")));
            }
        }
    }
    out
}

fn display_ty_body_for_lsp(ty: &Ty, names: &HashMap<TyVar, String>) -> String {
    match ty {
        Ty::Qualified(_, inner) => display_ty_body_for_lsp(inner, names),
        _ => display_ty_with_var_names(ty, names),
    }
}

fn type_var_names(scheme: &Scheme) -> HashMap<TyVar, String> {
    let mut vars = scheme.vars.clone();
    for var in free_type_vars_in_display_order(&scheme.ty) {
        if !vars.contains(&var) {
            vars.push(var);
        }
    }
    for constraint in &scheme.constraints {
        if !vars.contains(&constraint.var) {
            vars.push(constraint.var);
        }
    }

    vars.into_iter()
        .enumerate()
        .map(|(idx, var)| (var, type_var_name(idx)))
        .collect()
}

fn constraints_by_var(
    scheme: &Scheme,
    names: &HashMap<TyVar, String>,
) -> Vec<(String, Vec<String>)> {
    let mut grouped: Vec<(TyVar, Vec<String>)> = Vec::new();
    for constraint in &scheme.constraints {
        let resolved_var = constraint_var_for_hover(constraint, &scheme.ty);
        if let Some((_, traits)) = grouped.iter_mut().find(|(var, _)| *var == resolved_var) {
            if !traits.contains(&constraint.trait_name) {
                traits.push(constraint.trait_name.clone());
            }
        } else {
            grouped.push((resolved_var, vec![constraint.trait_name.clone()]));
        }
    }
    grouped.sort_by_key(|(var, _)| names.get(var).cloned().unwrap_or_else(|| var.to_string()));
    grouped
        .into_iter()
        .map(|(var, traits)| {
            (
                names.get(&var).cloned().unwrap_or_else(|| var.to_string()),
                traits,
            )
        })
        .collect()
}

fn constraint_var_for_hover(constraint: &TraitConstraint, ty: &Ty) -> TyVar {
    match ty {
        Ty::Qualified(_, inner) => match inner.as_ref() {
            Ty::Var(var) => *var,
            _ => constraint.var,
        },
        _ => constraint.var,
    }
}

fn type_declaration_hover_text(program: &Program, definition: &Definition) -> Option<String> {
    match definition.kind {
        DefinitionKind::Type => program.stmts.iter().find_map(|stmt| match stmt {
            Stmt::Type(type_def) if type_def.name_span == definition.location.span => {
                let params = type_params_suffix(&type_def.params);
                let variants = type_def
                    .variants
                    .iter()
                    .map(|variant| match &variant.payload {
                        Some(payload) => {
                            format!("{}({})", variant.name, ast_type_to_string(payload))
                        }
                        None => variant.name.clone(),
                    })
                    .collect::<Vec<_>>()
                    .join(" | ");
                Some(format!("type {}{} = {}", type_def.name, params, variants))
            }
            _ => None,
        }),
        DefinitionKind::TypeAlias => program.stmts.iter().find_map(|stmt| match stmt {
            Stmt::TypeAlias {
                name,
                name_span,
                params,
                ty,
                ..
            } if *name_span == definition.location.span => Some(format!(
                "type {}{} = {}",
                name,
                type_params_suffix(params),
                ast_type_to_string(ty)
            )),
            _ => None,
        }),
        DefinitionKind::Trait => program.stmts.iter().find_map(|stmt| match stmt {
            Stmt::Trait(trait_def) if trait_def.name_span == definition.location.span => {
                Some(format!("trait {} {}", trait_def.name, trait_def.param))
            }
            _ => None,
        }),
        DefinitionKind::TraitMethod => program.stmts.iter().find_map(|stmt| match stmt {
            Stmt::Trait(trait_def) => trait_def
                .methods
                .iter()
                .find(|method| method.name_span == definition.location.span)
                .map(trait_method_signature),
            _ => None,
        }),
        DefinitionKind::ImplMethod => program.stmts.iter().find_map(|stmt| match stmt {
            Stmt::Impl(impl_def) => impl_def
                .methods
                .iter()
                .find(|method| method.name_span == definition.location.span)
                .map(impl_method_signature),
            _ => None,
        }),
        _ => None,
    }
}

fn trait_method_signature(method: &hern_core::ast::TraitMethod) -> String {
    let params = method
        .params
        .iter()
        .map(|(name, ty)| format!("{name}: {}", ast_type_to_string(ty)))
        .collect::<Vec<_>>()
        .join(", ");
    format!(
        "fn {}({}) -> {}",
        method.name,
        params,
        ast_type_to_string(&method.ret_type)
    )
}

fn impl_method_signature(method: &ImplMethod) -> String {
    let params = method
        .params
        .iter()
        .map(|(pat, ty)| {
            let pat = pattern_to_string(pat);
            match ty {
                Some(ty) => format!("{pat}: {}", ast_type_to_string(ty)),
                None => pat,
            }
        })
        .collect::<Vec<_>>()
        .join(", ");
    match &method.ret_type {
        Some(ret) => format!(
            "fn {}({}) -> {}",
            method.name,
            params,
            ast_type_to_string(ret)
        ),
        None => format!("fn {}({})", method.name, params),
    }
}

fn type_params_suffix(params: &[String]) -> String {
    if params.is_empty() {
        String::new()
    } else {
        format!("({})", params.join(", "))
    }
}

fn ast_type_to_string(ty: &hern_core::ast::Type) -> String {
    use hern_core::ast::Type;
    match ty {
        Type::Ident(name) | Type::Var(name) => name.clone(),
        Type::App(con, args) => format!(
            "{}({})",
            ast_type_to_string(con),
            args.iter()
                .map(ast_type_to_string)
                .collect::<Vec<_>>()
                .join(", ")
        ),
        Type::Func(params, ret) => format!(
            "fn({}) -> {}",
            params
                .iter()
                .map(ast_type_to_string)
                .collect::<Vec<_>>()
                .join(", "),
            ast_type_to_string(ret)
        ),
        Type::Tuple(items) => format!(
            "({})",
            items
                .iter()
                .map(ast_type_to_string)
                .collect::<Vec<_>>()
                .join(", ")
        ),
        Type::Record(fields, is_open) => {
            let mut parts = fields
                .iter()
                .map(|(name, ty)| format!("{name}: {}", ast_type_to_string(ty)))
                .collect::<Vec<_>>();
            if *is_open {
                parts.push("..".to_string());
            }
            format!("#{{ {} }}", parts.join(", "))
        }
        Type::Unit => "()".to_string(),
        Type::Hole => "*".to_string(),
    }
}

fn pattern_to_string(pat: &Pattern) -> String {
    match pat {
        Pattern::Wildcard => "_".to_string(),
        Pattern::StringLit(value) => format!("{value:?}"),
        Pattern::Variable(name, _) => name.clone(),
        Pattern::Constructor { name, binding } => match binding {
            Some((binding, _)) => format!("{name}({binding})"),
            None => name.clone(),
        },
        Pattern::Record { fields, rest } => {
            let mut parts = fields
                .iter()
                .map(|(field, binding, _)| {
                    if field == binding {
                        field.clone()
                    } else {
                        format!("{field}: {binding}")
                    }
                })
                .collect::<Vec<_>>();
            match rest {
                Some(Some((name, _))) => parts.push(format!("..{name}")),
                Some(None) => parts.push("..".to_string()),
                None => {}
            }
            format!("#{{ {} }}", parts.join(", "))
        }
        Pattern::List { elements, rest } => {
            let mut parts = elements.iter().map(pattern_to_string).collect::<Vec<_>>();
            match rest {
                Some(Some((name, _))) => parts.push(format!("..{name}")),
                Some(None) => parts.push("..".to_string()),
                None => {}
            }
            format!("[{}]", parts.join(", "))
        }
        Pattern::Tuple(items) => format!(
            "({})",
            items
                .iter()
                .map(pattern_to_string)
                .collect::<Vec<_>>()
                .join(", ")
        ),
    }
}

/// Resolve the hover type for an imported module member.
///
/// Uses the module's export record type (`import_types`) rather than searching
/// by definition name, so it correctly handles aliased exports (`#{ public: private }`),
/// exported literals, and computed export expressions.
fn imported_member_hover_text(
    graph: &ModuleGraph,
    inference: &GraphInference,
    reference: &ImportMemberReference,
) -> Option<String> {
    // Primary path: look up the field from the module's concrete export type.
    // This is correct for all export shapes, including aliased names.
    if let Some(Ty::Record(row)) = inference.import_types.get(&reference.module_name) {
        if let Some((_, field_ty)) = row.fields.iter().find(|(f, _)| f == &reference.member_name) {
            return Some(ty_to_display_string(field_ty));
        }
    }

    // Fallback: definition-based lookup for non-record or unavailable export shapes.
    let target_program = graph.module(&reference.module_name)?;
    let target_index = index_program(target_program);
    let target_definition = target_index.definition_named(&reference.member_name)?;
    definition_hover_text(
        target_definition,
        inference.env_for_module(&reference.module_name),
        inference.expr_types_for_module(&reference.module_name),
        inference.binding_types_for_module(&reference.module_name),
        inference.definition_schemes_for_module(&reference.module_name),
        inference.variant_env_for_module(&reference.module_name),
        target_program,
    )
}

fn definition_hover_text(
    definition: &Definition,
    env: Option<&TypeEnv>,
    expr_types: Option<&HashMap<hern_core::ast::NodeId, Ty>>,
    binding_types: Option<&HashMap<SourceSpan, Ty>>,
    definition_schemes: Option<&HashMap<SourceSpan, Scheme>>,
    variant_env: Option<&VariantEnv>,
    program: &Program,
) -> Option<String> {
    if let Some(scheme) =
        definition_schemes.and_then(|schemes| schemes.get(&definition.location.span))
    {
        return Some(hover_scheme_to_string(scheme));
    }

    if matches!(
        definition.kind,
        DefinitionKind::Let | DefinitionKind::Parameter
    ) && let Some(ty) = binding_types.and_then(|types| types.get(&definition.location.span))
    {
        return Some(ty_to_display_string(ty));
    }

    // For parameter definitions, use ONLY the pattern-based type lookup.
    // Do NOT fall through to env.get(name): a same-named top-level binding would
    // produce a misleading type (lambda params, shadowed names, etc.).
    if definition.kind == DefinitionKind::Parameter {
        return param_hover_text(definition, program, env, expr_types, variant_env);
    }

    if let Some(info) = env.and_then(|env| env.get(&definition.name)) {
        return Some(hover_scheme_to_string(&info.scheme));
    }

    // For destructured local let/for/match bindings,
    // extract the specific binding type from the RHS via the pattern structure.
    if definition.kind == DefinitionKind::Let {
        if let Some(types) = expr_types {
            if let Some(ty) = local_pattern_binding_type(
                program,
                &definition.name,
                definition.location.span,
                types,
                binding_types,
                variant_env,
            ) {
                return Some(ty);
            }
        }
    }

    expr_types
        .and_then(|types| declaration_value_type(program, definition.location.span, types))
        .map(|ty| ty_to_display_string(ty))
        .or_else(|| type_declaration_hover_text(program, definition))
}

/// Given a Parameter definition, find the enclosing callable and return the
/// parameter's type as a string.
fn param_hover_text(
    definition: &Definition,
    program: &Program,
    env: Option<&TypeEnv>,
    expr_types: Option<&HashMap<hern_core::ast::NodeId, Ty>>,
    variant_env: Option<&VariantEnv>,
) -> Option<String> {
    let param_span = definition.location.span;
    for stmt in &program.stmts {
        if let Some(ty) = param_type_in_stmt(
            stmt,
            &definition.name,
            param_span,
            env,
            expr_types,
            variant_env,
        ) {
            return Some(ty);
        }
    }
    None
}

fn param_type_in_stmt(
    stmt: &Stmt,
    name: &str,
    param_span: SourceSpan,
    env: Option<&TypeEnv>,
    expr_types: Option<&HashMap<hern_core::ast::NodeId, Ty>>,
    variant_env: Option<&VariantEnv>,
) -> Option<String> {
    match stmt {
        Stmt::Fn {
            name: fn_name,
            params,
            ..
        }
        | Stmt::Op {
            name: fn_name,
            params,
            ..
        } => param_type_from_fn_scheme(fn_name, params, name, param_span, env, variant_env),
        Stmt::Impl(id) => {
            let dict_key = format!("__{}__{}", id.trait_name, impl_target_name(&id.target));
            for method in &id.methods {
                if let Some(ty) =
                    param_type_from_impl_dict(&dict_key, method, name, param_span, env, variant_env)
                {
                    return Some(ty);
                }
            }
            None
        }
        Stmt::Let { value, .. } => {
            param_type_in_expr_stmts(value, name, param_span, env, expr_types, variant_env)
        }
        Stmt::Expr(expr) => {
            param_type_in_expr_stmts(expr, name, param_span, env, expr_types, variant_env)
        }
        _ => None,
    }
}

/// Mirrors `impl_target_name` from the type inferencer.
fn impl_target_name(target: &hern_core::ast::Type) -> String {
    match target {
        hern_core::ast::Type::Ident(name) => name.clone(),
        hern_core::ast::Type::App(con, _) => impl_target_name(con),
        _ => "Unknown".to_string(),
    }
}

/// Find the param in `params` that owns the binding `(param_name, param_span)`, then
/// extract the concrete type of *that binding* from the function's scheme.
///
/// For a top-level `Variable` param the binding type is the whole param type.
/// For a `Record` param the binding type is the type of the matched field.
fn param_type_from_fn_scheme(
    fn_name: &str,
    params: &[(Pattern, Option<hern_core::ast::Type>)],
    param_name: &str,
    param_span: SourceSpan,
    env: Option<&TypeEnv>,
    variant_env: Option<&VariantEnv>,
) -> Option<String> {
    let param_idx = params
        .iter()
        .position(|(pat, _)| pattern_has_binding_at(pat, param_name, param_span))?;
    let param_pat = &params[param_idx].0;

    let scheme = env.and_then(|e| e.get(fn_name))?;
    let Ty::Func(param_tys, _) = &scheme.scheme.ty else {
        return None;
    };
    let param_ty = param_tys.get(param_idx)?;

    // Navigate through the pattern structure to find the type of the specific binding.
    let binding_ty =
        extract_binding_type(param_pat, param_name, param_span, param_ty, variant_env)?;
    let display_scheme = Scheme {
        vars: scheme.scheme.vars.clone(),
        constraints: scheme.scheme.constraints.clone(),
        ty: binding_ty,
    };
    Some(hover_scheme_to_string(&display_scheme))
}

/// Impl methods are stored in the type env as a trait dictionary: a record type
/// whose fields are the method names and whose field types are the method function
/// types.  Look up the dict, find the method's `Ty::Func`, then extract the
/// param binding type the same way as for ordinary functions.
fn param_type_from_impl_dict(
    dict_key: &str,
    method: &ImplMethod,
    param_name: &str,
    param_span: SourceSpan,
    env: Option<&TypeEnv>,
    variant_env: Option<&VariantEnv>,
) -> Option<String> {
    let param_idx = method
        .params
        .iter()
        .position(|(pat, _)| pattern_has_binding_at(pat, param_name, param_span))?;
    let param_pat = &method.params[param_idx].0;

    let dict_scheme = env.and_then(|e| e.get(dict_key))?;
    // The dict is stored as Ty::Record where each field is the method's Func type.
    let Ty::Record(row) = &dict_scheme.scheme.ty else {
        return None;
    };
    let method_ty = row
        .fields
        .iter()
        .find(|(f, _)| f == &method.name)
        .map(|(_, ty)| ty)?;
    let Ty::Func(param_tys, _) = method_ty else {
        return None;
    };
    let param_ty = param_tys.get(param_idx)?;

    let binding_ty =
        extract_binding_type(param_pat, param_name, param_span, param_ty, variant_env)?;
    let display_scheme = Scheme {
        vars: dict_scheme.scheme.vars.clone(),
        constraints: dict_scheme.scheme.constraints.clone(),
        ty: binding_ty,
    };
    Some(hover_scheme_to_string(&display_scheme))
}

/// Recursively navigate `pat` to find the sub-type corresponding to the binding
/// `(target_name, target_span)` within the type `param_ty`.
fn extract_binding_type(
    pat: &Pattern,
    target_name: &str,
    target_span: SourceSpan,
    param_ty: &Ty,
    variant_env: Option<&VariantEnv>,
) -> Option<Ty> {
    match pat {
        Pattern::Variable(n, s) if n == target_name && *s == target_span => Some(param_ty.clone()),
        Pattern::Record { fields, rest } => {
            let Ty::Record(row) = param_ty else {
                return None;
            };
            // Named field bindings.
            for (field_name, bind_name, bind_span) in fields {
                if bind_name == target_name && *bind_span == target_span {
                    return row
                        .fields
                        .iter()
                        .find(|(f, _)| f == field_name)
                        .map(|(_, ty)| ty.clone());
                }
            }
            // Rest binding `..rest` — its type is the remaining record fields
            // (those not bound by name in this pattern) plus the row's tail.
            if let Some(Some((rest_name, rest_span))) = rest {
                if rest_name == target_name && *rest_span == target_span {
                    let named: std::collections::HashSet<&str> =
                        fields.iter().map(|(f, _, _)| f.as_str()).collect();
                    let rest_fields: Vec<(String, Ty)> = row
                        .fields
                        .iter()
                        .filter(|(f, _)| !named.contains(f.as_str()))
                        .cloned()
                        .collect();
                    return Some(Ty::Record(hern_core::types::Row {
                        fields: rest_fields,
                        tail: row.tail.clone(),
                    }));
                }
            }
            None
        }
        Pattern::List { elements, rest } => {
            let Ty::App(con, args) = param_ty else {
                return None;
            };
            let Ty::Con(name) = con.as_ref() else {
                return None;
            };
            if name != "Array" {
                return None;
            }
            let elem_ty = args.first()?;
            for elem_pat in elements {
                if let Some(ty) =
                    extract_binding_type(elem_pat, target_name, target_span, elem_ty, variant_env)
                {
                    return Some(ty);
                }
            }
            if let Some(Some((rest_name, rest_span))) = rest {
                if rest_name == target_name && *rest_span == target_span {
                    return Some(param_ty.clone());
                }
            }
            None
        }
        // Tuple: element i binds to the i-th element type of a Ty::Tuple.
        Pattern::Tuple(elems) => {
            let Ty::Tuple(elem_tys) = param_ty else {
                return None;
            };
            for (elem_pat, elem_ty) in elems.iter().zip(elem_tys.iter()) {
                if let Some(ty) =
                    extract_binding_type(elem_pat, target_name, target_span, elem_ty, variant_env)
                {
                    return Some(ty);
                }
            }
            None
        }
        Pattern::Constructor { name, binding } => {
            if let Some((bind_name, bind_span)) = binding {
                if bind_name == target_name && *bind_span == target_span {
                    return constructor_payload_type(name, param_ty, variant_env);
                }
            }
            None
        }
        // Wildcards have no bindings; any other pattern is unreachable here after
        // the irrefutability check in the type inferencer.
        _ => None,
    }
}

/// Resolve the payload type of a constructor binding such as `Some(x)` or `Err(e)`.
///
/// Uses the variant environment to correctly map type parameters to their instantiated
/// types — for example, `Err(e)` in a `Result(f64, string)` correctly yields `string`
/// rather than the first type argument.
///
/// Falls back to a positional heuristic (`args[0]` / `args[1]` for `Err`) only when the
/// variant environment is unavailable.
fn constructor_payload_type(
    constructor: &str,
    outer_ty: &Ty,
    variant_env: Option<&VariantEnv>,
) -> Option<Ty> {
    let args = match outer_ty {
        Ty::App(_, args) => args.as_slice(),
        _ => &[],
    };

    if let Some(venv) = variant_env {
        if let Some(info) = venv.0.get(constructor) {
            if let Some(payload_ty) = &info.payload_ty {
                return Some(instantiate_variant_template(
                    payload_ty,
                    &info.type_param_vars,
                    args,
                ));
            }
        }
    }

    // Fallback when variant_env is unavailable: use the position heuristic
    // that works for Option('a) and Result('a, 'e).
    match outer_ty {
        Ty::App(_, args) if constructor == "Err" => args.get(1).cloned(),
        Ty::App(_, args) => args.first().cloned(),
        _ => None,
    }
}

fn instantiate_variant_template(
    template: &Ty,
    type_param_vars: &[hern_core::types::TyVar],
    args: &[Ty],
) -> Ty {
    match template {
        Ty::Var(var) => type_param_vars
            .iter()
            .position(|param_var| param_var == var)
            .and_then(|idx| args.get(idx).cloned())
            .unwrap_or(Ty::Var(*var)),
        Ty::Qualified(constraints, inner) => Ty::Qualified(
            constraints
                .iter()
                .filter_map(|constraint| {
                    let var = match type_param_vars
                        .iter()
                        .position(|param_var| param_var == &constraint.var)
                        .and_then(|idx| args.get(idx))
                    {
                        Some(Ty::Var(var)) => *var,
                        Some(_) => return None,
                        None => constraint.var,
                    };
                    Some(hern_core::types::TraitConstraint {
                        var,
                        trait_name: constraint.trait_name.clone(),
                    })
                })
                .collect(),
            Box::new(instantiate_variant_template(inner, type_param_vars, args)),
        ),
        Ty::Tuple(items) => Ty::Tuple(
            items
                .iter()
                .map(|ty| instantiate_variant_template(ty, type_param_vars, args))
                .collect(),
        ),
        Ty::Func(params, ret) => Ty::Func(
            params
                .iter()
                .map(|ty| instantiate_variant_template(ty, type_param_vars, args))
                .collect(),
            Box::new(instantiate_variant_template(ret, type_param_vars, args)),
        ),
        Ty::App(con, params) => Ty::App(
            Box::new(instantiate_variant_template(con, type_param_vars, args)),
            params
                .iter()
                .map(|ty| instantiate_variant_template(ty, type_param_vars, args))
                .collect(),
        ),
        Ty::Record(row) => Ty::Record(hern_core::types::Row {
            fields: row
                .fields
                .iter()
                .map(|(name, ty)| {
                    (
                        name.clone(),
                        instantiate_variant_template(ty, type_param_vars, args),
                    )
                })
                .collect(),
            tail: Box::new(instantiate_variant_template(
                &row.tail,
                type_param_vars,
                args,
            )),
        }),
        Ty::F64 | Ty::Unit | Ty::Con(_) => template.clone(),
    }
}

fn param_type_in_expr_stmts(
    expr: &Expr,
    name: &str,
    param_span: SourceSpan,
    env: Option<&TypeEnv>,
    expr_types: Option<&HashMap<hern_core::ast::NodeId, Ty>>,
    variant_env: Option<&VariantEnv>,
) -> Option<String> {
    match &expr.kind {
        ExprKind::Lambda { params, body } => {
            if let Some(idx) = params
                .iter()
                .position(|(pat, _)| pattern_has_binding_at(pat, name, param_span))
            {
                // Look up the lambda's Ty::Func from expr_types to get the param type.
                let types = expr_types?;
                let Ty::Func(param_tys, _) = types.get(&expr.id)? else {
                    return None;
                };
                let param_ty = param_tys.get(idx)?;
                let pat = &params[idx].0;
                return extract_binding_type(pat, name, param_span, param_ty, variant_env)
                    .map(|ty| ty_to_display_string(&ty));
            }
            param_type_in_expr_stmts(body, name, param_span, env, expr_types, variant_env)
        }
        ExprKind::Block { stmts, final_expr } => {
            for stmt in stmts {
                if let Some(ty) =
                    param_type_in_stmt(stmt, name, param_span, env, expr_types, variant_env)
                {
                    return Some(ty);
                }
            }
            final_expr.as_deref().and_then(|e| {
                param_type_in_expr_stmts(e, name, param_span, env, expr_types, variant_env)
            })
        }
        ExprKind::Not(e)
        | ExprKind::Loop(e)
        | ExprKind::Break(Some(e))
        | ExprKind::Return(Some(e))
        | ExprKind::FieldAccess { expr: e, .. } => {
            param_type_in_expr_stmts(e, name, param_span, env, expr_types, variant_env)
        }
        ExprKind::Assign { target, value }
        | ExprKind::Binary {
            lhs: target,
            rhs: value,
            ..
        } => param_type_in_expr_stmts(target, name, param_span, env, expr_types, variant_env)
            .or_else(|| {
                param_type_in_expr_stmts(value, name, param_span, env, expr_types, variant_env)
            }),
        ExprKind::Call { callee, args, .. } => {
            param_type_in_expr_stmts(callee, name, param_span, env, expr_types, variant_env)
                .or_else(|| {
                    args.iter().find_map(|a| {
                        param_type_in_expr_stmts(a, name, param_span, env, expr_types, variant_env)
                    })
                })
        }
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
        } => param_type_in_expr_stmts(cond, name, param_span, env, expr_types, variant_env)
            .or_else(|| {
                param_type_in_expr_stmts(
                    then_branch,
                    name,
                    param_span,
                    env,
                    expr_types,
                    variant_env,
                )
            })
            .or_else(|| {
                param_type_in_expr_stmts(
                    else_branch,
                    name,
                    param_span,
                    env,
                    expr_types,
                    variant_env,
                )
            }),
        ExprKind::Match { scrutinee, arms } => {
            param_type_in_expr_stmts(scrutinee, name, param_span, env, expr_types, variant_env)
                .or_else(|| {
                    arms.iter().find_map(|(_, body)| {
                        param_type_in_expr_stmts(
                            body,
                            name,
                            param_span,
                            env,
                            expr_types,
                            variant_env,
                        )
                    })
                })
        }
        ExprKind::Tuple(items) | ExprKind::Array(items) => items.iter().find_map(|item| {
            param_type_in_expr_stmts(item, name, param_span, env, expr_types, variant_env)
        }),
        ExprKind::Record(fields) => fields.iter().find_map(|(_, v)| {
            param_type_in_expr_stmts(v, name, param_span, env, expr_types, variant_env)
        }),
        ExprKind::For { iterable, body, .. } => {
            param_type_in_expr_stmts(iterable, name, param_span, env, expr_types, variant_env)
                .or_else(|| {
                    param_type_in_expr_stmts(body, name, param_span, env, expr_types, variant_env)
                })
        }
        ExprKind::Break(None)
        | ExprKind::Return(None)
        | ExprKind::Continue
        | ExprKind::Number(_)
        | ExprKind::StringLit(_)
        | ExprKind::Bool(_)
        | ExprKind::Ident(_)
        | ExprKind::Import(_)
        | ExprKind::Unit => None,
    }
}

fn pattern_has_binding_at(pat: &Pattern, name: &str, span: SourceSpan) -> bool {
    match pat {
        Pattern::Variable(n, s) => n == name && *s == span,
        Pattern::Constructor {
            binding: Some((n, s)),
            ..
        } => n == name && *s == span,
        Pattern::Record { fields, rest } => {
            fields.iter().any(|(_, b, s)| b == name && *s == span)
                || matches!(rest, Some(Some((n, s))) if n == name && *s == span)
        }
        Pattern::List { elements, rest } => {
            elements
                .iter()
                .any(|elem| pattern_has_binding_at(elem, name, span))
                || matches!(rest, Some(Some((n, s))) if n == name && *s == span)
        }
        Pattern::Tuple(elems) => elems.iter().any(|e| pattern_has_binding_at(e, name, span)),
        _ => false,
    }
}

/// Returns true if any binding span in `pat` equals `span`.
fn pattern_has_span_at(pat: &Pattern, span: SourceSpan) -> bool {
    match pat {
        Pattern::Variable(_, s) => *s == span,
        Pattern::Constructor {
            binding: Some((_, s)),
            ..
        } => *s == span,
        Pattern::Record { fields, rest } => {
            fields.iter().any(|(_, _, s)| *s == span)
                || matches!(rest, Some(Some((_, s))) if *s == span)
        }
        Pattern::List { elements, rest } => {
            elements.iter().any(|elem| pattern_has_span_at(elem, span))
                || matches!(rest, Some(Some((_, s))) if *s == span)
        }
        Pattern::Tuple(elems) => elems.iter().any(|e| pattern_has_span_at(e, span)),
        _ => false,
    }
}

/// For a local binding introduced by `let`, `for`, or `match`, recover the binding type
/// by traversing the expression and pattern structure.
fn local_pattern_binding_type(
    program: &Program,
    name: &str,
    binding_span: SourceSpan,
    expr_types: &HashMap<hern_core::ast::NodeId, Ty>,
    binding_types: Option<&HashMap<SourceSpan, Ty>>,
    variant_env: Option<&VariantEnv>,
) -> Option<String> {
    if let Some(ty) = binding_types.and_then(|types| types.get(&binding_span)) {
        return Some(ty_to_display_string(ty));
    }

    for stmt in &program.stmts {
        if let Some(ty) =
            local_pattern_binding_type_in_stmt(stmt, name, binding_span, expr_types, variant_env)
        {
            return Some(ty);
        }
    }
    None
}

fn local_pattern_binding_type_in_stmt(
    stmt: &Stmt,
    name: &str,
    binding_span: SourceSpan,
    expr_types: &HashMap<hern_core::ast::NodeId, Ty>,
    variant_env: Option<&VariantEnv>,
) -> Option<String> {
    match stmt {
        Stmt::Let { pat, value, .. } => {
            if !matches!(pat, Pattern::Variable(_, _) | Pattern::Wildcard)
                && pattern_has_binding_at(pat, name, binding_span)
            {
                if let Some(rhs_ty) = expr_types.get(&value.id) {
                    if let Some(binding_ty) =
                        extract_binding_type(pat, name, binding_span, rhs_ty, variant_env)
                    {
                        return Some(ty_to_display_string(&binding_ty));
                    }
                }
            }
            local_pattern_binding_type_in_expr(value, name, binding_span, expr_types, variant_env)
        }
        Stmt::Expr(value) => {
            local_pattern_binding_type_in_expr(value, name, binding_span, expr_types, variant_env)
        }
        Stmt::Fn { body, .. } | Stmt::Op { body, .. } => {
            local_pattern_binding_type_in_expr(body, name, binding_span, expr_types, variant_env)
        }
        Stmt::Impl(impl_def) => impl_def.methods.iter().find_map(|method| {
            local_pattern_binding_type_in_expr(
                &method.body,
                name,
                binding_span,
                expr_types,
                variant_env,
            )
        }),
        Stmt::Trait(_) | Stmt::Type(_) | Stmt::TypeAlias { .. } | Stmt::Extern { .. } => None,
    }
}

fn local_pattern_binding_type_in_expr(
    expr: &Expr,
    name: &str,
    binding_span: SourceSpan,
    expr_types: &HashMap<hern_core::ast::NodeId, Ty>,
    variant_env: Option<&VariantEnv>,
) -> Option<String> {
    match &expr.kind {
        ExprKind::For {
            pat,
            iterable,
            body,
            ..
        } => {
            if pattern_has_binding_at(pat, name, binding_span) {
                if let Some(iterable_ty) = expr_types.get(&iterable.id) {
                    if let Some(elem_ty) = iterable_element_type(iterable_ty) {
                        if let Some(binding_ty) =
                            extract_binding_type(pat, name, binding_span, elem_ty, variant_env)
                        {
                            return Some(ty_to_display_string(&binding_ty));
                        }
                    }
                }
            }
            local_pattern_binding_type_in_expr(
                iterable,
                name,
                binding_span,
                expr_types,
                variant_env,
            )
            .or_else(|| {
                local_pattern_binding_type_in_expr(
                    body,
                    name,
                    binding_span,
                    expr_types,
                    variant_env,
                )
            })
        }
        ExprKind::Block { stmts, final_expr } => {
            for stmt in stmts {
                if let Some(ty) = local_pattern_binding_type_in_stmt(
                    stmt,
                    name,
                    binding_span,
                    expr_types,
                    variant_env,
                ) {
                    return Some(ty);
                }
            }
            final_expr.as_deref().and_then(|e| {
                local_pattern_binding_type_in_expr(e, name, binding_span, expr_types, variant_env)
            })
        }
        ExprKind::Not(e)
        | ExprKind::Loop(e)
        | ExprKind::Break(Some(e))
        | ExprKind::Return(Some(e))
        | ExprKind::FieldAccess { expr: e, .. }
        | ExprKind::Lambda { body: e, .. } => {
            local_pattern_binding_type_in_expr(e, name, binding_span, expr_types, variant_env)
        }
        ExprKind::Assign { target, value }
        | ExprKind::Binary {
            lhs: target,
            rhs: value,
            ..
        } => {
            local_pattern_binding_type_in_expr(target, name, binding_span, expr_types, variant_env)
                .or_else(|| {
                    local_pattern_binding_type_in_expr(
                        value,
                        name,
                        binding_span,
                        expr_types,
                        variant_env,
                    )
                })
        }
        ExprKind::Call { callee, args, .. } => {
            local_pattern_binding_type_in_expr(callee, name, binding_span, expr_types, variant_env)
                .or_else(|| {
                    args.iter().find_map(|a| {
                        local_pattern_binding_type_in_expr(
                            a,
                            name,
                            binding_span,
                            expr_types,
                            variant_env,
                        )
                    })
                })
        }
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
        } => local_pattern_binding_type_in_expr(cond, name, binding_span, expr_types, variant_env)
            .or_else(|| {
                local_pattern_binding_type_in_expr(
                    then_branch,
                    name,
                    binding_span,
                    expr_types,
                    variant_env,
                )
            })
            .or_else(|| {
                local_pattern_binding_type_in_expr(
                    else_branch,
                    name,
                    binding_span,
                    expr_types,
                    variant_env,
                )
            }),
        ExprKind::Match { scrutinee, arms } => {
            for (pat, body) in arms {
                if pattern_has_binding_at(pat, name, binding_span) {
                    if let Some(scrutinee_ty) = expr_types.get(&scrutinee.id) {
                        if let Some(binding_ty) =
                            extract_binding_type(pat, name, binding_span, scrutinee_ty, variant_env)
                        {
                            return Some(ty_to_display_string(&binding_ty));
                        }
                    }
                }
                if let Some(ty) = local_pattern_binding_type_in_expr(
                    body,
                    name,
                    binding_span,
                    expr_types,
                    variant_env,
                ) {
                    return Some(ty);
                }
            }
            local_pattern_binding_type_in_expr(
                scrutinee,
                name,
                binding_span,
                expr_types,
                variant_env,
            )
        }
        ExprKind::Tuple(items) | ExprKind::Array(items) => items.iter().find_map(|item| {
            local_pattern_binding_type_in_expr(item, name, binding_span, expr_types, variant_env)
        }),
        ExprKind::Record(fields) => fields.iter().find_map(|(_, v)| {
            local_pattern_binding_type_in_expr(v, name, binding_span, expr_types, variant_env)
        }),
        ExprKind::Break(None)
        | ExprKind::Return(None)
        | ExprKind::Continue
        | ExprKind::Number(_)
        | ExprKind::StringLit(_)
        | ExprKind::Bool(_)
        | ExprKind::Ident(_)
        | ExprKind::Import(_)
        | ExprKind::Unit => None,
    }
}

fn iterable_element_type(iterable_ty: &Ty) -> Option<&Ty> {
    // Convention: for single-type-argument iterables (e.g. `Array[T]`), the element
    // type is the first type argument. This mirrors what the inferencer ultimately
    // extracts from the Iterable.iter return type for these cases.
    // Limitation: multi-parameter types where the element type is not the first
    // argument will show the wrong type. The principled fix is to record the loop
    // element type during inference and expose it in the output.
    match iterable_ty {
        Ty::App(_, args) if args.len() == 1 => args.first(),
        _ => None,
    }
}

fn declaration_value_type<'a>(
    program: &'a Program,
    span: SourceSpan,
    expr_types: &'a HashMap<hern_core::ast::NodeId, Ty>,
) -> Option<&'a Ty> {
    for stmt in &program.stmts {
        if let Some(ty) = declaration_value_type_in_stmt(stmt, span, expr_types) {
            return Some(ty);
        }
    }
    None
}

fn declaration_value_type_in_stmt<'a>(
    stmt: &'a Stmt,
    span: SourceSpan,
    expr_types: &'a HashMap<hern_core::ast::NodeId, Ty>,
) -> Option<&'a Ty> {
    match stmt {
        Stmt::Let { pat, value, .. } if pattern_has_span_at(pat, span) => expr_types.get(&value.id),
        Stmt::Fn {
            name_span, body, ..
        }
        | Stmt::Op {
            name_span, body, ..
        } if *name_span == span => expr_types.get(&body.id),
        Stmt::Expr(expr) => declaration_value_type_in_expr(expr, span, expr_types),
        Stmt::Impl(impl_def) => impl_def.methods.iter().find_map(|method| {
            (method.name_span == span)
                .then(|| expr_types.get(&method.body.id))
                .flatten()
        }),
        Stmt::Trait(_) | Stmt::Type(_) | Stmt::TypeAlias { .. } | Stmt::Extern { .. } => None,
        Stmt::Let { value, .. } => declaration_value_type_in_expr(value, span, expr_types),
        Stmt::Fn { body, .. } | Stmt::Op { body, .. } => {
            declaration_value_type_in_expr(body, span, expr_types)
        }
    }
}

fn declaration_value_type_in_expr<'a>(
    expr: &'a Expr,
    span: SourceSpan,
    expr_types: &'a HashMap<hern_core::ast::NodeId, Ty>,
) -> Option<&'a Ty> {
    match &expr.kind {
        ExprKind::Block { stmts, final_expr } => {
            for stmt in stmts {
                if let Some(ty) = declaration_value_type_in_stmt(stmt, span, expr_types) {
                    return Some(ty);
                }
            }
            final_expr
                .as_deref()
                .and_then(|expr| declaration_value_type_in_expr(expr, span, expr_types))
        }
        ExprKind::Not(expr)
        | ExprKind::Loop(expr)
        | ExprKind::Break(Some(expr))
        | ExprKind::Return(Some(expr))
        | ExprKind::FieldAccess { expr, .. }
        | ExprKind::Lambda { body: expr, .. } => {
            declaration_value_type_in_expr(expr, span, expr_types)
        }
        ExprKind::Assign { target, value }
        | ExprKind::Binary {
            lhs: target,
            rhs: value,
            ..
        } => declaration_value_type_in_expr(target, span, expr_types)
            .or_else(|| declaration_value_type_in_expr(value, span, expr_types)),
        ExprKind::Call { callee, args, .. } => {
            declaration_value_type_in_expr(callee, span, expr_types).or_else(|| {
                args.iter()
                    .find_map(|arg| declaration_value_type_in_expr(arg, span, expr_types))
            })
        }
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
        } => declaration_value_type_in_expr(cond, span, expr_types)
            .or_else(|| declaration_value_type_in_expr(then_branch, span, expr_types))
            .or_else(|| declaration_value_type_in_expr(else_branch, span, expr_types)),
        ExprKind::Match { scrutinee, arms } => {
            declaration_value_type_in_expr(scrutinee, span, expr_types).or_else(|| {
                arms.iter()
                    .find_map(|(_, body)| declaration_value_type_in_expr(body, span, expr_types))
            })
        }
        ExprKind::Tuple(items) | ExprKind::Array(items) => items
            .iter()
            .find_map(|item| declaration_value_type_in_expr(item, span, expr_types)),
        ExprKind::Record(fields) => fields
            .iter()
            .find_map(|(_, value)| declaration_value_type_in_expr(value, span, expr_types)),
        ExprKind::For { iterable, body, .. } => {
            declaration_value_type_in_expr(iterable, span, expr_types)
                .or_else(|| declaration_value_type_in_expr(body, span, expr_types))
        }
        ExprKind::Break(None)
        | ExprKind::Return(None)
        | ExprKind::Continue
        | ExprKind::Number(_)
        | ExprKind::StringLit(_)
        | ExprKind::Bool(_)
        | ExprKind::Ident(_)
        | ExprKind::Import(_)
        | ExprKind::Unit => None,
    }
}

pub(crate) fn definition(state: &ServerState, uri: Uri, position: Position) -> Option<Location> {
    let path = uri_to_path(&uri)?;
    let fallback;
    let graph = if let Some(analysis) = cached_analysis(state, &uri) {
        &analysis.graph
    } else {
        fallback = load_document_graph(state, &uri).ok()?;
        &fallback.0
    };
    let (_, program) = graph.module_for_path(&path)?;
    let index = index_program(program);
    let position = SourcePosition {
        line: position.line as usize + 1,
        col: position.character as usize + 1,
    };
    if let Some(reference) = index.import_member_reference_at(position) {
        let target_program = graph.module(&reference.module_name)?;
        let target_path = graph.module_path(&reference.module_name)?;
        let target_index = index_program(target_program);
        let target_definition = target_index.definition_named(&reference.member_name)?;
        return Some(Location::new(
            path_to_uri(target_path)?,
            source_span_to_range(target_definition.location.span),
        ));
    }
    let definition = index.definition_for_reference_at(SourcePosition {
        line: position.line,
        col: position.col,
    })?;
    Some(Location::new(
        uri,
        source_span_to_range(definition.location.span),
    ))
}

pub(crate) fn references(
    state: &ServerState,
    uri: Uri,
    position: Position,
    include_declaration: bool,
) -> Vec<Location> {
    let Some(path) = uri_to_path(&uri) else {
        return Vec::new();
    };
    let fallback;
    let graph = if let Some(analysis) = cached_analysis(state, &uri) {
        &analysis.graph
    } else {
        let Ok(loaded) = load_document_graph(state, &uri) else {
            return Vec::new();
        };
        fallback = loaded;
        &fallback.0
    };
    let Some((_, program)) = graph.module_for_path(&path) else {
        return Vec::new();
    };
    let index = index_program(program);
    let position = SourcePosition {
        line: position.line as usize + 1,
        col: position.character as usize + 1,
    };

    if let Some(import_ref) = index.import_member_reference_at(position) {
        let module_name = import_ref.module_name.clone();
        let member_name = import_ref.member_name.clone();
        references_for_import_member(graph, &module_name, &member_name, include_declaration)
    } else {
        let spans = index.references_for_symbol_at(position, include_declaration);
        spans
            .into_iter()
            .map(|span| Location::new(uri.clone(), source_span_to_range(span)))
            .collect()
    }
}

/// Collects all `Location`s for references to `member_name` exported from `module_name`,
/// scanning every module in the graph in graph order. Optionally includes the definition site
/// in the target module when `include_declaration` is true.
fn references_for_import_member(
    graph: &ModuleGraph,
    module_name: &str,
    member_name: &str,
    include_declaration: bool,
) -> Vec<Location> {
    let mut locations = Vec::new();

    if include_declaration && let Some(target_program) = graph.module(module_name) {
        let target_index = index_program(target_program);
        if let Some(def) = target_index.definition_named(member_name)
            && let Some(target_path) = graph.module_path(module_name)
            && let Some(target_uri) = path_to_uri(target_path)
        {
            locations.push(Location::new(
                target_uri,
                source_span_to_range(def.location.span),
            ));
        }
    }

    for name in &graph.order {
        let Some(prog) = graph.module(name) else {
            continue;
        };
        let prog_index = index_program(prog);
        let mut spans = prog_index.import_member_references_for(module_name, member_name);
        if spans.is_empty() {
            continue;
        }
        let Some(module_path) = graph.module_path(name) else {
            continue;
        };
        let Some(module_uri) = path_to_uri(module_path) else {
            continue;
        };
        spans.sort_by_key(|s| (s.start_line, s.start_col));
        for span in spans {
            locations.push(Location::new(
                module_uri.clone(),
                source_span_to_range(span),
            ));
        }
    }

    locations
}

/// Returns `true` if `name` is a well-formed Hern identifier that is not a reserved keyword.
///
/// The keyword list and identifier character rules mirror `hern_core::lex`. If the lexer gains
/// new keywords, this list must be updated to match.
fn is_valid_identifier(name: &str) -> bool {
    if name.is_empty() {
        return false;
    }
    const KEYWORDS: &[&str] = &[
        "let", "mut", "fn", "if", "else", "trait", "impl", "for", "type", "match", "loop", "break",
        "continue", "return", "extern", "import", "true", "false", "in",
    ];
    if KEYWORDS.contains(&name) {
        return false;
    }
    let mut bytes = name.bytes();
    let first = bytes.next().unwrap();
    if !first.is_ascii_alphabetic() && first != b'_' {
        return false;
    }
    bytes.all(|b| b.is_ascii_alphanumeric() || b == b'_')
}

fn renameable_definition_kind(kind: DefinitionKind) -> bool {
    matches!(kind, DefinitionKind::Function | DefinitionKind::Let)
}

/// Renames the symbol at `position` in `uri` to `new_name`.
///
/// Returns `Ok(Some(edit))` on success, `Ok(None)` if the cursor is not on a known symbol,
/// and `Err(message)` for invalid names or unsupported rename targets (imported members).
pub(crate) fn rename(
    state: &ServerState,
    uri: Uri,
    position: Position,
    new_name: String,
) -> Result<Option<WorkspaceEdit>, String> {
    if !is_valid_identifier(&new_name) {
        return Err(format!("invalid identifier: {:?}", new_name));
    }
    let Some(path) = uri_to_path(&uri) else {
        return Ok(None);
    };
    let fallback;
    let graph = if let Some(analysis) = cached_analysis(state, &uri) {
        &analysis.graph
    } else {
        let Ok(loaded) = load_document_graph(state, &uri) else {
            return Ok(None);
        };
        fallback = loaded;
        &fallback.0
    };
    let Some((_, program)) = graph.module_for_path(&path) else {
        return Ok(None);
    };
    let index = index_program(program);
    let position = SourcePosition {
        line: position.line as usize + 1,
        col: position.character as usize + 1,
    };
    // Reject rename when the cursor is on a *member access* of an imported module (e.g. `dep.value`),
    // because the definition lives in another file and cross-file rename is out of scope for now.
    // Renaming the import binding itself (e.g. `dep` in `let dep = import "dep"`) is allowed: it
    // is just a local let binding resolved by references_for_symbol_at like any other local.
    if index.import_member_reference_at(position).is_some() {
        return Err("rename of imported members is not supported".to_string());
    }
    let Some(definition) = index
        .definition_at(position)
        .or_else(|| index.definition_for_reference_at(position))
    else {
        return Ok(None);
    };
    if !renameable_definition_kind(definition.kind) {
        return Err(format!(
            "rename is not supported for {:?} symbols",
            definition.kind
        ));
    }
    let spans = index.references_for_symbol_at(position, true);
    if spans.is_empty() {
        return Ok(None);
    }
    let edits: Vec<TextEdit> = spans
        .into_iter()
        .map(|span| TextEdit {
            range: source_span_to_range(span),
            new_text: new_name.clone(),
        })
        .collect();
    let mut changes = HashMap::new();
    changes.insert(uri, edits);
    Ok(Some(WorkspaceEdit {
        changes: Some(changes),
        ..Default::default()
    }))
}

/// Returns completion candidates visible at `position` in `uri`.
///
/// Tries three sources in order:
/// 1. Cached analysis (graph + type inference) — full type details.
/// 2. Fresh analysis (`analyze_document_graph`) — full type details when cache is stale.
/// 3. Recovering graph load (`load_document_graph_recovering`) — names without type details.
///    Used when inference fails or the file has a syntax error (e.g. mid-edit).
///
/// Returns an empty vec if the URI cannot be resolved or the file fails to parse entirely.
pub(crate) fn completion(state: &ServerState, uri: Uri, position: Position) -> Vec<CompletionItem> {
    let Some(path) = uri_to_path(&uri) else {
        return Vec::new();
    };

    let full_fallback;
    let partial_fallback;
    let parse_fallback;
    let default_inference;

    let (graph, inference) = if let Some(cached) = cached_analysis(state, &uri) {
        (&cached.graph, &cached.inference)
    } else if let Ok(wa) = analyze_document_graph(state, &uri) {
        full_fallback = wa;
        (&full_fallback.graph, &full_fallback.inference)
    } else {
        let analysis = analyze_workspace(WorkspaceInputs {
            entry: path.clone(),
            overlays: document_overlays(state),
            prelude: Some(state.prelude.program.clone()),
        });
        if let (Some(graph), Some(inference)) = (analysis.graph, analysis.inference) {
            partial_fallback = WorkspaceAnalysis { graph, inference };
            (&partial_fallback.graph, &partial_fallback.inference)
        } else if let Some(g) = load_document_graph_recovering(state, &uri) {
            default_inference = GraphInference::default();
            parse_fallback = g;
            (&parse_fallback, &default_inference)
        } else {
            return Vec::new();
        }
    };

    let Some((module_name, program)) = graph.module_for_path(&path) else {
        return Vec::new();
    };

    let lsp_position = position;
    let position = SourcePosition {
        line: lsp_position.line as usize + 1,
        col: lsp_position.character as usize + 1,
    };

    let index = index_program(program);
    let candidates = index.visible_names_at(position);
    let env = inference.env_for_module(module_name);
    let binding_types = inference.binding_types_for_module(module_name);
    let definition_schemes = inference.definition_schemes_for_module(module_name);
    let replacement_range = completion_replacement_range(state, &uri, lsp_position);

    candidates
        .into_iter()
        .map(|candidate| {
            let detail = completion_detail(
                &index,
                &candidate.name,
                position,
                env,
                binding_types,
                definition_schemes,
            );
            let kind = Some(match candidate.kind {
                CompletionCandidateKind::Function => CompletionItemKind::FUNCTION,
                CompletionCandidateKind::ImportBinding => CompletionItemKind::MODULE,
                _ => CompletionItemKind::VARIABLE,
            });
            CompletionItem {
                label: candidate.name.clone(),
                kind,
                filter_text: Some(candidate.name.clone()),
                insert_text: Some(candidate.name.clone()),
                text_edit: replacement_range.map(|range| {
                    CompletionTextEdit::Edit(TextEdit {
                        range,
                        new_text: candidate.name.clone(),
                    })
                }),
                label_details: detail.as_ref().map(|detail| CompletionItemLabelDetails {
                    detail: Some(format!(": {detail}")),
                    description: None,
                }),
                detail,
                ..Default::default()
            }
        })
        .collect()
}

fn completion_replacement_range(
    state: &ServerState,
    uri: &Uri,
    position: Position,
) -> Option<Range> {
    let line = state
        .documents
        .get(uri)?
        .lines()
        .nth(position.line as usize)?;
    let cursor_byte = utf16_col_to_byte(line, position.character);
    let start_byte = line[..cursor_byte.min(line.len())]
        .rfind(|c: char| !is_completion_identifier_char(c))
        .map(|idx| idx + 1)
        .unwrap_or(0);
    Some(Range::new(
        Position::new(position.line, byte_to_utf16_col(line, start_byte)),
        position,
    ))
}

fn is_completion_identifier_char(c: char) -> bool {
    c.is_ascii_alphanumeric() || c == '_'
}

fn utf16_col_to_byte(line: &str, col: u32) -> usize {
    let mut utf16 = 0u32;
    for (byte_idx, ch) in line.char_indices() {
        if utf16 >= col {
            return byte_idx;
        }
        utf16 += ch.len_utf16() as u32;
        if utf16 > col {
            return byte_idx;
        }
    }
    line.len()
}

fn byte_to_utf16_col(line: &str, byte: usize) -> u32 {
    line[..byte.min(line.len())]
        .chars()
        .map(|ch| ch.len_utf16() as u32)
        .sum()
}

fn completion_detail(
    index: &hern_core::source_index::SourceIndex,
    name: &str,
    position: SourcePosition,
    env: Option<&TypeEnv>,
    binding_types: Option<&HashMap<SourceSpan, Ty>>,
    definition_schemes: Option<&HashMap<SourceSpan, Scheme>>,
) -> Option<String> {
    let definition = visible_definition_named(index, name, position);
    if let Some(definition) = definition {
        if let Some(scheme) =
            definition_schemes.and_then(|schemes| schemes.get(&definition.location.span))
        {
            return Some(completion_scheme_to_string(scheme));
        }
        if matches!(
            definition.kind,
            DefinitionKind::Let | DefinitionKind::Parameter
        ) && let Some(ty) = binding_types.and_then(|types| types.get(&definition.location.span))
        {
            return Some(completion_ty_to_display_string(ty));
        }
    }

    env.and_then(|e| e.get(name))
        .map(|info| completion_scheme_to_string(&info.scheme))
}

fn visible_definition_named<'a>(
    index: &'a hern_core::source_index::SourceIndex,
    name: &str,
    position: SourcePosition,
) -> Option<&'a Definition> {
    let mut best = None;
    for definition in index
        .definitions
        .iter()
        .filter(|definition| definition.name == name)
    {
        if !matches!(
            definition.kind,
            DefinitionKind::Function
                | DefinitionKind::Let
                | DefinitionKind::Parameter
                | DefinitionKind::Extern
        ) {
            continue;
        }
        let visible = definition.visibility_end.line == usize::MAX || {
            let start = (
                definition.visibility_start.line,
                definition.visibility_start.col,
            );
            let end = (
                definition.visibility_end.line,
                definition.visibility_end.col,
            );
            let cursor = (position.line, position.col);
            cursor >= start && cursor < end
        };
        if visible {
            best = Some(definition);
        }
    }
    best
}

pub(crate) fn uri_to_path(uri: &Uri) -> Option<PathBuf> {
    if !uri.scheme()?.as_str().eq_ignore_ascii_case("file") {
        return None;
    }
    let path = percent_decode(uri.path().as_str())?;
    Some(PathBuf::from(path))
}

pub(crate) fn path_to_uri(path: &Path) -> Option<Uri> {
    Uri::from_str(&format!("file://{}", percent_encode_path(path))).ok()
}

fn diagnostics_from_compiler_diagnostics(
    entry_uri: &Uri,
    diagnostics: Vec<CompilerDiagnostic>,
) -> DiagnosticsByUri {
    let mut by_uri = DiagnosticsByUri::new();
    by_uri.insert(entry_uri.clone(), Vec::new());
    for diagnostic in diagnostics {
        let uri = diagnostic_source_uri(&diagnostic).unwrap_or_else(|| entry_uri.clone());
        by_uri
            .entry(uri)
            .or_default()
            .push(compiler_diagnostic_to_lsp(diagnostic));
    }
    by_uri
}

fn diagnostic_identity(diagnostic: &Diagnostic) -> String {
    format!(
        "{:?}:{:?}:{}",
        diagnostic.range, diagnostic.severity, diagnostic.message
    )
}

struct WorkspaceAnalysis {
    graph: ModuleGraph,
    inference: GraphInference,
}

fn analyze_document_graph(
    state: &ServerState,
    uri: &Uri,
) -> Result<WorkspaceAnalysis, CompilerDiagnostic> {
    let (mut graph, _) = load_document_graph(state, uri)?;
    let inference = infer_graph(&mut graph)?;
    Ok(WorkspaceAnalysis { graph, inference })
}

fn load_document_graph(
    state: &ServerState,
    uri: &Uri,
) -> Result<(ModuleGraph, String), CompilerDiagnostic> {
    let path = uri_to_path(uri).ok_or_else(|| {
        CompilerDiagnostic::error(None, format!("unsupported document URI: {}", uri.as_str()))
    })?;
    let overlays = document_overlays(state);
    ModuleGraph::load_entry_with_prelude_and_overlays(
        &path,
        state.prelude.program.clone(),
        overlays,
    )
}

/// Loads the module graph using parse-error recovery. Unlike `load_document_graph`, this
/// can return a partial graph even when the current document overlay has a syntax error —
/// making it suitable as a last-resort fallback for completion while the user is mid-edit.
/// Lex errors or missing entry-module paths can still cause this to return `None`.
fn load_document_graph_recovering(state: &ServerState, uri: &Uri) -> Option<ModuleGraph> {
    let path = uri_to_path(uri)?;
    let overlays = document_overlays(state);
    ModuleGraph::load_entry_with_prelude_and_overlays_recovering(
        &path,
        state.prelude.program.clone(),
        overlays,
    )
    .value
    .map(|loaded| loaded.graph)
}

fn cached_analysis<'a>(state: &'a ServerState, entry_uri: &Uri) -> Option<&'a CachedAnalysis> {
    let analysis = state.cached_analyses.get(entry_uri)?;
    analysis
        .document_versions
        .iter()
        .all(|(uri, version)| state.document_versions.get(uri) == Some(version))
        .then_some(analysis)
}

fn document_overlays(state: &ServerState) -> HashMap<PathBuf, String> {
    state
        .documents
        .iter()
        .filter_map(|(uri, source)| {
            let path = uri_to_path(uri)?;
            let canonical = fs::canonicalize(path).ok()?;
            Some((canonical, source.clone()))
        })
        .collect()
}

fn graph_module_uris(graph: &ModuleGraph) -> HashSet<Uri> {
    graph
        .paths
        .values()
        .filter_map(|p| path_to_uri(p))
        .collect()
}

fn document_versions_for_uris(state: &ServerState, uris: &HashSet<Uri>) -> HashMap<Uri, i32> {
    uris.iter()
        .filter_map(|uri| {
            let version = state.document_versions.get(uri)?;
            Some((uri.clone(), *version))
        })
        .collect()
}

fn percent_decode(value: &str) -> Option<String> {
    let bytes = value.as_bytes();
    let mut out = Vec::with_capacity(bytes.len());
    let mut idx = 0;
    while idx < bytes.len() {
        if bytes[idx] == b'%' {
            let hi = *bytes.get(idx + 1)?;
            let lo = *bytes.get(idx + 2)?;
            out.push(hex_val(hi)? << 4 | hex_val(lo)?);
            idx += 3;
        } else {
            out.push(bytes[idx]);
            idx += 1;
        }
    }
    String::from_utf8(out).ok()
}

fn hex_val(byte: u8) -> Option<u8> {
    match byte {
        b'0'..=b'9' => Some(byte - b'0'),
        b'a'..=b'f' => Some(byte - b'a' + 10),
        b'A'..=b'F' => Some(byte - b'A' + 10),
        _ => None,
    }
}

fn span_to_position(line: usize, col: usize) -> Position {
    Position::new(line.saturating_sub(1) as u32, col.saturating_sub(1) as u32)
}

fn compiler_diagnostic_to_lsp(diagnostic: CompilerDiagnostic) -> Diagnostic {
    let range = diagnostic
        .span
        .map(source_span_to_range)
        .unwrap_or_else(|| Range::new(Position::new(0, 0), Position::new(0, 0)));
    Diagnostic {
        range,
        severity: Some(match diagnostic.severity {
            CoreDiagnosticSeverity::Error => DiagnosticSeverity::ERROR,
        }),
        message: diagnostic.message,
        ..Default::default()
    }
}

fn source_span_to_range(span: SourceSpan) -> Range {
    Range::new(
        span_to_position(span.start_line, span.start_col),
        span_to_position(span.end_line, span.end_col),
    )
}

fn diagnostic_source_uri(diagnostic: &CompilerDiagnostic) -> Option<Uri> {
    let DiagnosticSource::Path(path) = diagnostic.source.as_ref()? else {
        return None;
    };
    path_to_uri(path)
}

fn percent_encode_path(path: &Path) -> String {
    let path = path.to_string_lossy();
    let mut out = String::with_capacity(path.len());
    for byte in path.bytes() {
        match byte {
            b'A'..=b'Z' | b'a'..=b'z' | b'0'..=b'9' | b'-' | b'.' | b'_' | b'~' | b'/' => {
                out.push(byte as char)
            }
            _ => out.push_str(&format!("%{byte:02X}")),
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use lsp_types::Uri;
    use std::time::{SystemTime, UNIX_EPOCH};

    fn uri(value: &str) -> Uri {
        Uri::from_str(value).expect("test URI should parse")
    }

    fn diagnostic(message: &str) -> Diagnostic {
        Diagnostic {
            range: Range::new(Position::new(0, 0), Position::new(0, 1)),
            severity: Some(DiagnosticSeverity::ERROR),
            message: message.to_string(),
            ..Default::default()
        }
    }

    fn temp_dir(name: &str) -> PathBuf {
        let path = std::env::temp_dir().join(format!(
            "hern-lsp-{name}-{}-{}",
            std::process::id(),
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .expect("system time should be after epoch")
                .as_nanos()
        ));
        fs::create_dir_all(&path).expect("temp test directory should be created");
        path
    }

    fn state_with_document(uri: Uri, source: String) -> ServerState {
        let mut state = ServerState::new().expect("server state should initialize");
        state.set_document(uri.clone(), source, 0);
        state.mark_open_entry(uri);
        state
    }

    struct TestProject {
        root: PathBuf,
    }

    impl TestProject {
        fn new(name: &str) -> Self {
            Self {
                root: temp_dir(name),
            }
        }

        fn write(&self, relative_path: &str, source: &str) -> Uri {
            let path = self.root.join(relative_path);
            if let Some(parent) = path.parent() {
                fs::create_dir_all(parent).expect("test parent directory should be created");
            }
            fs::write(&path, source).expect("test source should be written");
            path_to_uri(&fs::canonicalize(&path).expect("test path should canonicalize"))
                .expect("test URI should encode")
        }

        fn open(&self, relative_path: &str, source: &str) -> (ServerState, Uri) {
            let uri = self.write(relative_path, source);
            (state_with_document(uri.clone(), source.to_string()), uri)
        }
    }

    struct ImportFixture {
        state: ServerState,
        entry_uri: Uri,
        dep_uri: Uri,
    }

    fn import_fixture(name: &str, entry_source: &str, dep_source: &str) -> ImportFixture {
        let project = TestProject::new(name);
        let entry_uri = project.write("main.hern", entry_source);
        let dep_uri = project.write("dep.hern", dep_source);
        let state = state_with_document(entry_uri.clone(), entry_source.to_string());

        ImportFixture {
            state,
            entry_uri,
            dep_uri,
        }
    }

    fn hover_text(hover: Hover) -> String {
        match hover.contents {
            HoverContents::Markup(MarkupContent { value, .. }) => {
                // Strip the ```hern ... ``` fences added by type_hover.
                value
                    .trim()
                    .strip_prefix("```hern\n")
                    .and_then(|s| s.strip_suffix("\n```"))
                    .unwrap_or(&value)
                    .to_string()
            }
            other => panic!("unexpected hover contents: {other:?}"),
        }
    }

    fn completion_insert_name(item: &CompletionItem) -> &str {
        item.insert_text.as_deref().unwrap_or(&item.label)
    }

    #[test]
    fn diagnostics_from_compiler_diagnostics_routes_source_path_to_that_uri() {
        let entry = uri("file:///workspace/main.hern");
        let dep_path = PathBuf::from("/workspace/dep.hern");
        let diagnostic = CompilerDiagnostic::error_in(
            DiagnosticSource::Path(dep_path),
            Some(SourceSpan {
                start_line: 1,
                start_col: 1,
                end_line: 1,
                end_col: 2,
            }),
            "dep failed",
        );

        let diagnostics = diagnostics_from_compiler_diagnostics(&entry, vec![diagnostic]);
        let dep = uri("file:///workspace/dep.hern");

        assert!(diagnostics.get(&entry).is_some_and(Vec::is_empty));
        assert_eq!(diagnostics[&dep].len(), 1);
        assert_eq!(diagnostics[&dep][0].message, "dep failed");
    }

    #[test]
    fn combined_diagnostics_keep_other_entry_contributions() {
        let dep = uri("file:///workspace/dep.hern");
        let entry_a = uri("file:///workspace/a.hern");
        let entry_b = uri("file:///workspace/b.hern");

        let mut state = ServerState {
            documents: HashMap::new(),
            document_versions: HashMap::new(),
            diagnostics_by_entry: HashMap::new(),
            entry_dependencies: HashMap::new(),
            cached_analyses: HashMap::new(),
            open_entry_uris: HashSet::new(),
            prelude: analyze_prelude().expect("prelude should analyze"),
            supports_markdown_hover: true,
        };
        state.diagnostics_by_entry.insert(
            entry_a.clone(),
            HashMap::from([(dep.clone(), vec![diagnostic("a")])]),
        );
        state.diagnostics_by_entry.insert(
            entry_b.clone(),
            HashMap::from([(dep.clone(), vec![diagnostic("b")])]),
        );

        state.diagnostics_by_entry.remove(&entry_a);
        let combined = combined_diagnostics_for_uri(&state, &dep);

        assert_eq!(combined.len(), 1);
        assert_eq!(combined[0].message, "b");
    }

    #[test]
    fn diagnostics_for_document_reports_multiple_parse_errors() {
        let entry = uri("file:///workspace/main.hern");
        let mut state = ServerState {
            documents: HashMap::from([(entry.clone(), "let a = ;\nlet b = ;\n".to_string())]),
            document_versions: HashMap::from([(entry.clone(), 0)]),
            diagnostics_by_entry: HashMap::new(),
            entry_dependencies: HashMap::new(),
            cached_analyses: HashMap::new(),
            open_entry_uris: HashSet::new(),
            prelude: analyze_prelude().expect("prelude should analyze"),
            supports_markdown_hover: true,
        };

        let diagnostics = diagnostics_for_document(&mut state, &entry);
        let entry_diagnostics = diagnostics
            .get(&entry)
            .expect("parse diagnostics should target entry URI");

        assert_eq!(entry_diagnostics.len(), 2);
        assert_eq!(entry_diagnostics[0].range.start.line, 0);
        assert_eq!(entry_diagnostics[1].range.start.line, 1);

        state.documents.clear();
    }

    #[test]
    fn diagnostics_for_document_reports_imported_parse_errors() {
        let ImportFixture {
            mut state,
            entry_uri,
            dep_uri,
        } = import_fixture(
            "import-recovery",
            "let dep = import \"dep\";\n",
            "let a = ;\nlet b = ;\n",
        );

        let diagnostics = diagnostics_for_document(&mut state, &entry_uri);
        let dep_diagnostics = diagnostics
            .get(&dep_uri)
            .expect("imported diagnostics should target dep URI");

        assert_eq!(dep_diagnostics.len(), 2);
        assert_eq!(dep_diagnostics[0].range.start.line, 0);
        assert_eq!(dep_diagnostics[1].range.start.line, 1);
    }

    #[test]
    fn diagnostics_for_document_reports_missing_semicolon_in_function_body() {
        // The recovering parser treats the unsemiconed expression as a stmt and continues,
        // but must still emit a diagnostic so the user sees the error.
        let entry = uri("file:///workspace/main.hern");
        let source = "fn sum(steps) {\n  let mut total = 0;\n  total\n  total\n}\n";
        let mut state = ServerState {
            documents: HashMap::from([(entry.clone(), source.to_string())]),
            document_versions: HashMap::from([(entry.clone(), 0)]),
            diagnostics_by_entry: HashMap::new(),
            entry_dependencies: HashMap::new(),
            cached_analyses: HashMap::new(),
            open_entry_uris: HashSet::new(),
            prelude: analyze_prelude().expect("prelude should analyze"),
            supports_markdown_hover: true,
        };

        let diagnostics = diagnostics_for_document(&mut state, &entry);
        let entry_diagnostics = diagnostics
            .get(&entry)
            .expect("diagnostics should target entry URI");

        assert!(
            !entry_diagnostics.is_empty(),
            "missing semicolon should produce a diagnostic; got none"
        );
        let messages: Vec<_> = entry_diagnostics
            .iter()
            .map(|d| d.message.as_str())
            .collect();
        assert!(
            messages.iter().any(|m| m.contains("`;`")),
            "expected a missing-semicolon diagnostic; got {:?}",
            messages
        );

        state.documents.clear();
    }

    #[test]
    fn diagnostics_record_entry_dependencies() {
        let ImportFixture {
            mut state,
            entry_uri,
            dep_uri,
        } = import_fixture(
            "entry-dependencies",
            "let dep = import \"dep\";\ndep.value\n",
            "#{ value: 1 }\n",
        );

        let diagnostics = diagnostics_for_document(&mut state, &entry_uri);

        assert!(diagnostics[&entry_uri].is_empty());
        assert!(
            state
                .entry_dependencies
                .get(&entry_uri)
                .is_some_and(|dependencies| dependencies.contains(&dep_uri))
        );
        assert!(
            state
                .entries_affected_by_document(&dep_uri)
                .contains(&entry_uri)
        );
    }

    #[test]
    fn imported_document_change_invalidates_dependent_entry_cache() {
        let ImportFixture {
            mut state,
            entry_uri,
            dep_uri,
        } = import_fixture(
            "dependency-cache-invalidation",
            "let dep = import \"dep\";\ndep.value\n",
            "#{ value: 1 }\n",
        );

        diagnostics_for_document(&mut state, &entry_uri);
        assert!(state.cached_analyses.contains_key(&entry_uri));

        state.set_document(dep_uri, "#{ value: 2 }\n".to_string(), 1);

        assert!(!state.cached_analyses.contains_key(&entry_uri));
    }

    #[test]
    fn unrelated_document_change_keeps_entry_cache_usable() {
        let project = TestProject::new("unrelated-cache-invalidation");
        let entry_a_source = "let dep = import \"dep_a\";\ndep.value\n";
        let entry_b_source = "let dep = import \"dep_b\";\ndep.value\n";
        let entry_a_uri = project.write("main_a.hern", entry_a_source);
        let entry_b_uri = project.write("main_b.hern", entry_b_source);
        let dep_a_uri = project.write("dep_a.hern", "#{ value: 1 }\n");
        project.write("dep_b.hern", "#{ value: 2 }\n");
        let mut state = ServerState::new().expect("server state should initialize");
        state.set_document(entry_a_uri.clone(), entry_a_source.to_string(), 0);
        state.set_document(entry_b_uri.clone(), entry_b_source.to_string(), 0);

        diagnostics_for_document(&mut state, &entry_a_uri);
        diagnostics_for_document(&mut state, &entry_b_uri);
        assert!(cached_analysis(&state, &entry_a_uri).is_some());
        assert!(cached_analysis(&state, &entry_b_uri).is_some());

        state.set_document(dep_a_uri, "#{ value: 3 }\n".to_string(), 1);

        assert!(cached_analysis(&state, &entry_a_uri).is_none());
        assert!(cached_analysis(&state, &entry_b_uri).is_some());
    }

    #[test]
    fn imported_open_document_changes_entry_diagnostics_without_disk_write() {
        let ImportFixture {
            mut state,
            entry_uri,
            dep_uri,
        } = import_fixture(
            "dependency-overlay-diagnostics",
            "let dep = import \"dep\";\ndep.value\n",
            "#{ value: 1 }\n",
        );

        assert!(diagnostics_for_document(&mut state, &entry_uri)[&entry_uri].is_empty());

        state.set_document(dep_uri.clone(), "let broken = ;\n".to_string(), 1);
        let diagnostics = diagnostics_for_document(&mut state, &entry_uri);
        let dep_diagnostics = diagnostics
            .get(&dep_uri)
            .expect("dependency diagnostics should target the dependency URI");

        assert_eq!(dep_diagnostics.len(), 1);
    }

    #[test]
    fn hover_returns_inferred_type_for_local_expression() {
        let project = TestProject::new("local-hover");
        let source = "let value = 1;\nvalue\n";
        let (state, uri) = project.open("main.hern", source);

        let info = hover(&state, uri, Position::new(1, 1)).expect("hover should resolve");

        assert_eq!(hover_text(info), "f64");
    }

    #[test]
    fn hover_normalizes_free_type_vars_for_expressions() {
        let project = TestProject::new("normalized-expression-hover");
        let source = "[]\n";
        let (state, uri) = project.open("main.hern", source);

        let info = hover(&state, uri, Position::new(0, 1)).expect("hover should resolve");

        assert_eq!(hover_text(info), "['a]");
    }

    #[test]
    fn display_names_type_vars_by_visible_type_order() {
        let ty = Ty::Func(
            vec![Ty::Var(78), Ty::Tuple(vec![Ty::Var(12), Ty::Var(78)])],
            Box::new(Ty::Var(12)),
        );

        assert_eq!(ty_to_display_string(&ty), "fn('a, ('b, 'a)) -> 'b");
    }

    #[test]
    fn hover_reuses_type_var_names_within_polymorphic_function() {
        let project = TestProject::new("polymorphic-function-hover");
        let source = "fn choose(x, y) { x }\nchoose\n";
        let (state, uri) = project.open("main.hern", source);

        let info = hover(&state, uri, Position::new(1, 1)).expect("hover should resolve");

        assert_eq!(hover_text(info), "fn('a, 'b) -> 'a");
    }

    #[test]
    fn hover_uses_partial_inference_when_module_has_type_errors() {
        let project = TestProject::new("partial-hover");
        let source = "let value = 1;\nlet bad: bool = 2;\nvalue\n";
        let (state, uri) = project.open("main.hern", source);

        let info = hover(&state, uri, Position::new(2, 1)).expect("hover should resolve");

        assert_eq!(hover_text(info), "f64");
    }

    #[test]
    fn hover_returns_impl_method_signature() {
        let project = TestProject::new("impl-method-hover");
        let source = concat!(
            "trait Bump 'a {\n",
            "  fn bump(x: 'a) -> 'a\n",
            "}\n",
            "impl Bump for f64 {\n",
            "  fn bump(x: f64) -> f64 { x + 1 }\n",
            "}\n",
        );
        let (state, uri) = project.open("main.hern", source);

        let info = hover(&state, uri, Position::new(4, 5)).expect("hover should resolve");

        assert_eq!(hover_text(info), "fn(f64) -> f64");
    }

    #[test]
    fn hover_returns_type_and_trait_declarations() {
        let project = TestProject::new("type-trait-hover");
        let source = concat!(
            "type Pair = #{ x: f64, y: f64 }\n",
            "type Option2('a) = Some2('a) | None2\n",
            "trait Show 'a {\n",
            "  fn show(x: 'a) -> string\n",
            "}\n",
        );
        let (state, uri) = project.open("main.hern", source);

        let alias = hover(&state, uri.clone(), Position::new(0, 6)).expect("alias hover");
        let sum = hover(&state, uri.clone(), Position::new(1, 6)).expect("type hover");
        let trait_info = hover(&state, uri.clone(), Position::new(2, 7)).expect("trait hover");
        let trait_method = hover(&state, uri, Position::new(3, 5)).expect("trait method hover");

        assert_eq!(hover_text(alias), "type Pair = #{ x: f64, y: f64 }");
        assert_eq!(hover_text(sum), "type Option2('a) = Some2('a) | None2");
        assert_eq!(hover_text(trait_info), "trait Show 'a");
        assert_eq!(hover_text(trait_method), "fn show(x: 'a) -> string");
    }

    #[test]
    fn hover_uses_imported_module_types() {
        let source = "let dep = import \"dep\";\ndep.value()\n";
        let ImportFixture {
            state, entry_uri, ..
        } = import_fixture(
            "import-hover",
            source,
            "fn value() { 1 }\n#{ value: value }\n",
        );

        let info = hover(&state, entry_uri, Position::new(1, 10)).expect("hover should resolve");

        assert_eq!(hover_text(info), "f64");
    }

    #[test]
    fn hover_prefers_callee_symbol_type_inside_call() {
        let project = TestProject::new("callee-hover");
        let source = "fn identity(x) { x }\nidentity(1)\n";
        let (state, uri) = project.open("main.hern", source);

        let callee =
            hover(&state, uri.clone(), Position::new(1, 1)).expect("callee hover should resolve");
        let call = hover(&state, uri, Position::new(1, 10)).expect("call hover should resolve");

        assert_eq!(hover_text(callee), "fn(f64) -> f64");
        assert_eq!(hover_text(call), "f64");
    }

    #[test]
    fn hover_shows_callee_type_for_constrained_function_call() {
        // `sum` uses a `for` loop, giving it an `Iterable` constraint. The constrained
        // call path in the inferencer must still record the callee's type in symbol_types
        // so that hovering the callee shows the function type rather than the call result.
        let project = TestProject::new("constrained-callee-hover");
        let source = concat!(
            "fn sum(xs) {\n",
            "  let mut acc = 0;\n",
            "  for x in xs { acc = acc + x; }\n",
            "  acc\n",
            "}\n",
            "sum([1, 2, 3])\n",
        );
        let (state, uri) = project.open("main.hern", source);

        // Hover on "sum" in `sum([1, 2, 3])` — col 1 is the 's'
        let callee =
            hover(&state, uri.clone(), Position::new(5, 1)).expect("callee hover should resolve");
        // Hover on the call result — past the closing paren
        let call =
            hover(&state, uri, Position::new(5, 5)).expect("call result hover should resolve");

        let callee_text = hover_text(callee);
        // The callee type should be the function, not the return value ()
        assert!(
            callee_text.contains("fn("),
            "expected function type, got: {callee_text}"
        );
        assert!(
            callee_text.contains("Constraints:\n- 'a: Iterable"),
            "expected constraints section, got: {callee_text}"
        );
        assert_eq!(hover_text(call), "f64");
    }

    #[test]
    fn hover_groups_multiple_constraints_by_type_variable() {
        let project = TestProject::new("multi-constraint-hover");
        let source = concat!(
            "trait ConstraintA 'a {\n",
            "  fn a(x: 'a) -> 'a\n",
            "}\n",
            "trait ConstraintB 'a {\n",
            "  fn b(x: 'a) -> 'a\n",
            "}\n",
            "fn both ['a: ConstraintA + ConstraintB](x: 'a) -> 'a { x }\n",
        );
        let (state, uri) = project.open("main.hern", source);

        let info = hover(&state, uri, Position::new(6, 3)).expect("hover should resolve");

        assert_eq!(
            hover_text(info),
            "fn('a) -> 'a\n\nConstraints:\n- 'a: ConstraintA + ConstraintB"
        );
    }

    #[test]
    fn hover_returns_signature_for_function_declaration_name() {
        let project = TestProject::new("fn-declaration-hover");
        let source = "fn identity(x) { x }\nidentity(1)\n";
        let (state, uri) = project.open("main.hern", source);

        let info = hover(&state, uri, Position::new(0, 3)).expect("hover should resolve");

        let text = hover_text(info);
        assert_eq!(text, "fn('a) -> 'a");
    }

    #[test]
    fn hover_returns_type_for_let_declaration_name() {
        let project = TestProject::new("let-declaration-hover");
        let source = "let value = 1;\nvalue\n";
        let (state, uri) = project.open("main.hern", source);

        let info = hover(&state, uri, Position::new(0, 4)).expect("hover should resolve");

        assert_eq!(hover_text(info), "f64");
    }

    #[test]
    fn hover_returns_type_for_assignment_lvalue() {
        let project = TestProject::new("assignment-lvalue-hover");
        let source = "let mut value = 1;\nvalue = 2;\n";
        let (state, uri) = project.open("main.hern", source);

        let info = hover(&state, uri, Position::new(1, 1)).expect("hover should resolve");

        assert_eq!(hover_text(info), "f64");
    }

    #[test]
    fn hover_returns_element_type_for_for_loop_binding() {
        let project = TestProject::new("for-binding-hover");
        let source = concat!(
            "fn sum(steps) {\n",
            "  for step in steps {\n",
            "    step + 1\n",
            "  }\n",
            "}\n",
            "sum([1, 2])\n",
        );
        let (state, uri) = project.open("main.hern", source);

        let info = hover(&state, uri, Position::new(1, 6)).expect("hover should resolve");

        assert_eq!(hover_text(info), "f64");
    }

    #[test]
    fn hover_returns_binding_type_inside_structured_for_pattern() {
        let project = TestProject::new("for-pattern-hover");
        let source = concat!(
            "fn total(pairs) {\n",
            "  for (x, y) in pairs {\n",
            "    x + y + 1\n",
            "  }\n",
            "}\n",
            "total([(1, 2)])\n",
        );
        let (state, uri) = project.open("main.hern", source);

        let x_info = hover(&state, uri.clone(), Position::new(1, 7)).expect("hover should resolve");
        let y_info = hover(&state, uri, Position::new(1, 10)).expect("hover should resolve");

        assert_eq!(hover_text(x_info), "f64");
        assert_eq!(hover_text(y_info), "f64");
    }

    #[test]
    fn hover_returns_field_type_inside_record_for_pattern() {
        let project = TestProject::new("for-record-pattern-hover");
        let source = concat!(
            "fn total(rows) {\n",
            "  for #{ a, .. } in rows {\n",
            "    a + 1\n",
            "  }\n",
            "}\n",
            "total([#{ a: 1, b: 2 }])\n",
        );
        let (state, uri) = project.open("main.hern", source);

        let info = hover(&state, uri, Position::new(1, 9)).expect("hover should resolve");

        assert_eq!(hover_text(info), "f64");
    }

    #[test]
    fn hover_returns_type_for_plain_function_parameter() {
        // `x + 1` with the literal `1 :: f64` forces `x` to be `f64`,
        // so the parameter type is fully concrete and hover shows it directly.
        let project = TestProject::new("fn-param-hover");
        let source = "fn add_one(x) { x + 1 }\nadd_one(1)\n";
        let (state, uri) = project.open("main.hern", source);

        // "fn add_one(" = 11 chars; `x` is at col 11 on line 0.
        let info = hover(&state, uri, Position::new(0, 11)).expect("hover should resolve");

        assert_eq!(hover_text(info), "f64");
    }

    #[test]
    fn hover_returns_payload_type_for_match_some_binding() {
        // Hover on the `v` binding inside `Some(v)` in a match arm.
        let project = TestProject::new("match-some-hover");
        let source = concat!(
            "fn wrap(x) { Some(x) }\n", // line 0
            "match wrap(1) {\n",        // line 1
            "  Some(v) -> v + 1,\n",    // line 2: `v` at col 7
            "  None -> 0,\n",           // line 3
            "}\n",                      // line 4
        );
        let (state, uri) = project.open("main.hern", source);

        let info = hover(&state, uri, Position::new(2, 7)).expect("hover should resolve");

        assert_eq!(hover_text(info), "f64");
    }

    #[test]
    fn hover_returns_correct_type_for_match_ok_and_err_bindings() {
        // `Ok(v)` should give the first Result type argument (f64),
        // `Err(e)` should give the *second* type argument (string) — this validates
        // that the variant-env lookup picks the right type param, not always args[0].
        let project = TestProject::new("match-result-hover");
        let source = concat!(
            "fn safe_div(a, b) {\n",                             // line 0
            "  if b == 0 { Err(\"bad\") } else { Ok(a / b) }\n", // line 1
            "}\n",                                               // line 2
            "match safe_div(10, 2) {\n",                         // line 3
            "  Ok(v) -> v,\n",                                   // line 4: `v` at col 5
            "  Err(e) -> 0,\n",                                  // line 5: `e` at col 6
            "}\n",                                               // line 6
        );
        let (state, uri) = project.open("main.hern", source);

        let ok_info =
            hover(&state, uri.clone(), Position::new(4, 5)).expect("Ok hover should resolve");
        let err_info = hover(&state, uri, Position::new(5, 6)).expect("Err hover should resolve");

        assert_eq!(hover_text(ok_info), "f64");
        assert_eq!(hover_text(err_info), "string");
    }

    #[test]
    fn hover_resolves_constructor_payload_type_aliases() {
        let project = TestProject::new("match-aliased-payload-hover");
        let source = concat!(
            "type Amount = f64\n",
            "type Wrapped = Wrap(Amount) | Empty\n",
            "match Wrap(1) {\n",
            "  Wrap(v) -> v + 1,\n",
            "  Empty -> 0,\n",
            "}\n",
        );
        let (state, uri) = project.open("main.hern", source);

        let info = hover(&state, uri, Position::new(3, 7)).expect("hover should resolve");

        assert_eq!(hover_text(info), "f64");
    }

    #[test]
    fn hover_returns_imported_member_signature() {
        let source = "let dep = import \"dep\";\ndep.value()\n";
        let ImportFixture {
            state, entry_uri, ..
        } = import_fixture(
            "imported-member-hover",
            source,
            "fn value() { 1 }\n#{ value: value }\n",
        );

        let info = hover(&state, entry_uri, Position::new(1, 5)).expect("hover should resolve");

        assert_eq!(hover_text(info), "fn() -> f64");
    }

    #[test]
    fn diagnostics_cache_successful_analysis_for_hover_reuse() {
        let project = TestProject::new("analysis-cache");
        let source = "let value = 1;\nvalue\n";
        let (mut state, uri) = project.open("main.hern", source);

        assert!(state.cached_analyses.is_empty());
        let diagnostics = diagnostics_for_document(&mut state, &uri);

        assert!(diagnostics[&uri].is_empty());
        assert!(state.cached_analyses.contains_key(&uri));
        let info = hover(&state, uri, Position::new(1, 1)).expect("hover should resolve");
        assert_eq!(hover_text(info), "f64");
    }

    #[test]
    fn diagnostics_do_not_cache_partial_analysis() {
        let project = TestProject::new("analysis-cache-diagnostics");
        let source = "let value: bool = 1;\nvalue\n";
        let (mut state, uri) = project.open("main.hern", source);

        let diagnostics = diagnostics_for_document(&mut state, &uri);

        assert_eq!(diagnostics[&uri].len(), 1);
        assert!(state.cached_analyses.is_empty());
    }

    #[test]
    fn document_change_invalidates_cached_analysis() {
        let project = TestProject::new("analysis-cache-invalidated");
        let source = "let value = 1;\nvalue\n";
        let (mut state, uri) = project.open("main.hern", source);

        diagnostics_for_document(&mut state, &uri);

        assert!(state.cached_analyses.contains_key(&uri));
        state.set_document(uri.clone(), "let value = 2;\nvalue\n".to_string(), 1);

        assert!(state.cached_analyses.is_empty());
        assert_eq!(state.document_versions[&uri], 1);
    }

    #[test]
    fn definition_resolves_top_level_symbol_in_same_module() {
        let project = TestProject::new("definition-top-level");
        let source = "fn value() { 1 }\nvalue()\n";
        let (state, uri) = project.open("main.hern", source);

        let location = definition(&state, uri.clone(), Position::new(1, 1))
            .expect("definition should resolve");

        assert_eq!(location.uri, uri);
        assert_eq!(location.range.start, Position::new(0, 3));
    }

    #[test]
    fn definition_resolves_local_symbol_in_same_module() {
        let project = TestProject::new("definition-local");
        let source = "{ let value = 1; value }\n";
        let (state, uri) = project.open("main.hern", source);

        let location = definition(&state, uri.clone(), Position::new(0, 18))
            .expect("definition should resolve");

        assert_eq!(location.uri, uri);
        assert_eq!(location.range.start, Position::new(0, 6));
    }

    #[test]
    fn definition_resolves_imported_member_symbol() {
        let source = "let dep = import \"dep\";\ndep.value()\n";
        let ImportFixture {
            state,
            entry_uri,
            dep_uri,
        } = import_fixture(
            "definition-import",
            source,
            "fn value() { 1 }\n#{ value: value }\n",
        );
        let location =
            definition(&state, entry_uri, Position::new(1, 5)).expect("definition should resolve");

        assert_eq!(location.uri, dep_uri);
        assert_eq!(location.range.start, Position::new(0, 3));
    }

    #[test]
    fn references_returns_same_module_uses_without_declaration() {
        let project = TestProject::new("references-local");
        let source = "let value = 1;\nvalue\nvalue\n";
        let (state, uri) = project.open("main.hern", source);

        let locs = references(&state, uri.clone(), Position::new(0, 4), false);

        // two uses on lines 2 and 3; declaration on line 1 is excluded
        assert_eq!(locs.len(), 2);
        assert!(locs.iter().all(|l| l.uri == uri));
        assert_eq!(locs[0].range.start.line, 1);
        assert_eq!(locs[1].range.start.line, 2);
    }

    #[test]
    fn references_honors_include_declaration_true() {
        let project = TestProject::new("references-include-decl");
        let source = "fn value() { 1 }\nvalue()\n";
        let (state, uri) = project.open("main.hern", source);

        let locs = references(&state, uri.clone(), Position::new(1, 1), true);

        // declaration (line 1) + use (line 2)
        assert_eq!(locs.len(), 2);
        assert_eq!(locs[0].range.start.line, 0);
        assert_eq!(locs[1].range.start.line, 1);
    }

    #[test]
    fn references_returns_empty_for_unknown_position() {
        let project = TestProject::new("references-empty");
        let source = "let value = 1;\n";
        let (state, uri) = project.open("main.hern", source);

        let locs = references(&state, uri, Position::new(99, 0), false);

        assert!(locs.is_empty());
    }

    #[test]
    fn references_returns_imported_member_uses() {
        let source = "let dep = import \"dep\";\ndep.value\ndep.value\n";
        let ImportFixture {
            state, entry_uri, ..
        } = import_fixture(
            "references-import-member",
            source,
            "fn value() { 1 }\n#{ value: value }\n",
        );
        let locs = references(&state, entry_uri.clone(), Position::new(1, 4), false);

        assert_eq!(locs.len(), 2);
        assert!(locs.iter().all(|l| l.uri == entry_uri));
    }

    #[test]
    fn references_imported_member_include_declaration_adds_target_definition() {
        let source = "let dep = import \"dep\";\ndep.value\n";
        let ImportFixture {
            state,
            entry_uri,
            dep_uri,
        } = import_fixture(
            "references-import-decl",
            source,
            "fn value() { 1 }\n#{ value: value }\n",
        );
        let locs = references(&state, entry_uri.clone(), Position::new(1, 4), true);

        assert_eq!(locs.len(), 2);
        assert!(locs.iter().any(|l| l.uri == dep_uri));
        assert!(locs.iter().any(|l| l.uri == entry_uri));
    }

    #[test]
    fn unsaved_overlay_changes_diagnostics_without_disk_write() {
        let project = TestProject::new("overlay-diagnostics");
        let uri = project.write("main.hern", "let value = 1;\n");
        let mut state = state_with_document(uri.clone(), "let a = ;\nlet b = ;\n".to_string());
        let diagnostics = diagnostics_for_document(&mut state, &uri);
        let entry_diagnostics = diagnostics
            .get(&uri)
            .expect("overlay parse diagnostics should target entry");

        assert_eq!(entry_diagnostics.len(), 2);
    }

    #[test]
    fn type_mismatch_diagnostic_has_nonzero_range() {
        let project = TestProject::new("type-range");
        let source = "let value: bool = 1;\n";
        let (mut state, uri) = project.open("main.hern", source);

        let diagnostics = diagnostics_for_document(&mut state, &uri);
        let diagnostic = diagnostics
            .values()
            .flat_map(|items| items.iter())
            .next()
            .expect("type diagnostic should be reported");

        assert!(diagnostic.range.end.character > diagnostic.range.start.character);
    }

    #[test]
    fn rename_local_let_edits_declaration_and_use() {
        let project = TestProject::new("rename-local-let");
        let source = "{ let value = 1; value }\n";
        let (state, uri) = project.open("main.hern", source);

        let edit = rename(
            &state,
            uri.clone(),
            Position::new(0, 6),
            "amount".to_string(),
        )
        .expect("rename should succeed")
        .expect("rename should return edits");

        let edits = edit.changes.expect("changes should be present");
        let file_edits = edits.get(&uri).expect("edits for file should be present");
        assert_eq!(file_edits.len(), 2);
        assert!(file_edits.iter().all(|e| e.new_text == "amount"));
        // declaration before use in source order
        assert!(file_edits[0].range.start < file_edits[1].range.start);
    }

    #[test]
    fn rename_function_edits_declaration_and_call() {
        let project = TestProject::new("rename-fn");
        let source = "fn value() { 1 }\nvalue()\n";
        let (state, uri) = project.open("main.hern", source);

        let edit = rename(
            &state,
            uri.clone(),
            Position::new(1, 1),
            "compute".to_string(),
        )
        .expect("rename should succeed")
        .expect("rename should return edits");

        let edits = edit.changes.expect("changes should be present");
        let file_edits = edits.get(&uri).expect("edits for file should be present");
        assert_eq!(file_edits.len(), 2);
        assert!(file_edits.iter().all(|e| e.new_text == "compute"));
        assert_eq!(file_edits[0].range.start.line, 0); // declaration
        assert_eq!(file_edits[1].range.start.line, 1); // call
    }

    #[test]
    fn rename_respects_shadowing_inner() {
        let project = TestProject::new("rename-shadow-inner");
        let source = "let value = 1;\n{ let value = 2; value };\nvalue\n";
        let (state, uri) = project.open("main.hern", source);

        let edit = rename(
            &state,
            uri.clone(),
            Position::new(1, 17),
            "inner".to_string(),
        )
        .expect("rename should succeed")
        .expect("rename should return edits");

        let edits = edit.changes.expect("changes should be present");
        let file_edits = edits.get(&uri).expect("edits for file should be present");
        // only inner declaration and inner use — both on line 2 (0-indexed line 1)
        assert_eq!(file_edits.len(), 2);
        assert!(file_edits.iter().all(|e| e.range.start.line == 1));
    }

    #[test]
    fn rename_respects_shadowing_outer() {
        let project = TestProject::new("rename-shadow-outer");
        let source = "let value = 1;\n{ let value = 2; value };\nvalue\n";
        let (state, uri) = project.open("main.hern", source);

        let edit = rename(
            &state,
            uri.clone(),
            Position::new(0, 4),
            "outer".to_string(),
        )
        .expect("rename should succeed")
        .expect("rename should return edits");

        let edits = edit.changes.expect("changes should be present");
        let file_edits = edits.get(&uri).expect("edits for file should be present");
        // outer declaration (line 1) and outer use (line 3); inner binding is separate
        assert_eq!(file_edits.len(), 2);
        assert!(
            file_edits
                .iter()
                .all(|e| e.range.start.line == 0 || e.range.start.line == 2)
        );
    }

    #[test]
    fn rename_cursor_not_on_symbol_returns_none() {
        let project = TestProject::new("rename-no-symbol");
        let source = "let value = 1;\n";
        let (state, uri) = project.open("main.hern", source);

        let result = rename(&state, uri, Position::new(0, 10), "x".to_string())
            .expect("rename should not error");

        assert!(result.is_none());
    }

    #[test]
    fn rename_invalid_name_returns_error() {
        let project = TestProject::new("rename-invalid");
        let source = "let value = 1;\n";
        let (state, uri) = project.open("main.hern", source);

        assert!(rename(&state, uri.clone(), Position::new(0, 4), "1bad".to_string()).is_err());
        assert!(rename(&state, uri.clone(), Position::new(0, 4), "let".to_string()).is_err());
        assert!(rename(&state, uri.clone(), Position::new(0, 4), String::new()).is_err());
    }

    #[test]
    fn rename_imported_member_returns_error() {
        let source = "let dep = import \"dep\";\ndep.value\n";
        let ImportFixture {
            state, entry_uri, ..
        } = import_fixture(
            "rename-import-member",
            source,
            "fn value() { 1 }\n#{ value: value }\n",
        );
        let result = rename(
            &state,
            entry_uri,
            Position::new(1, 4),
            "renamed".to_string(),
        );

        assert!(result.is_err());
    }

    #[test]
    fn rename_type_definition_returns_error() {
        let project = TestProject::new("rename-type");
        let source = "type Option('a) = None | Some('a)\n";
        let (state, uri) = project.open("main.hern", source);

        let result = rename(&state, uri, Position::new(0, 5), "Maybe".to_string());

        assert!(result.is_err());
    }

    #[test]
    fn completion_returns_top_level_names() {
        let project = TestProject::new("completion-top-level");
        let source = "fn greet() { 1 }\nlet count = 42;\ngreet()\n";
        let (state, uri) = project.open("main.hern", source);

        let items = completion(&state, uri, Position::new(2, 1));

        let names: Vec<_> = items.iter().map(completion_insert_name).collect();
        assert!(
            names.contains(&"greet"),
            "greet should be a completion candidate"
        );
        assert!(
            names.contains(&"count"),
            "count should be a completion candidate"
        );
    }

    #[test]
    fn completion_returns_block_local_inside_scope() {
        let project = TestProject::new("completion-block-local");
        let source = "fn run() { let total = 1; total }\n";
        let (state, uri) = project.open("main.hern", source);

        let items = completion(&state, uri, Position::new(0, 26));

        let names: Vec<_> = items.iter().map(completion_insert_name).collect();
        assert!(names.contains(&"total"), "total should be in scope");
        assert!(
            names.contains(&"run"),
            "run should be in scope as a top-level fn"
        );
    }

    #[test]
    fn completion_shadowing_returns_inner_binding() {
        let project = TestProject::new("completion-shadow");
        let source = "let x = 1;\n{ let x = 2; x }\n";
        let (state, uri) = project.open("main.hern", source);

        let items = completion(&state, uri, Position::new(1, 13));

        let x_items: Vec<_> = items
            .iter()
            .filter(|i| completion_insert_name(i) == "x")
            .collect();
        assert_eq!(
            x_items.len(),
            1,
            "exactly one `x` candidate (inner shadows outer)"
        );
        // inner `x` is a VARIABLE (Local), outer top-level would also be VARIABLE so both map the same
        assert_eq!(x_items[0].kind, Some(CompletionItemKind::VARIABLE));
    }

    #[test]
    fn completion_import_binding_has_module_kind() {
        let source = "let dep = import \"dep\";\ndep\n";
        let ImportFixture {
            state, entry_uri, ..
        } = import_fixture(
            "completion-import-binding",
            source,
            "fn value() { 1 }\n#{ value: value }\n",
        );

        let items = completion(&state, entry_uri, Position::new(1, 0));

        let dep_item = items
            .iter()
            .find(|i| completion_insert_name(i) == "dep")
            .expect("dep binding should appear in completion");
        assert_eq!(dep_item.kind, Some(CompletionItemKind::MODULE));
    }

    #[test]
    fn completion_provides_type_detail_for_top_level_function() {
        let project = TestProject::new("completion-type-detail");
        let source = "fn double(x: f64) -> f64 { x + x }\ndouble(1)\n";
        let (state, uri) = project.open("main.hern", source);

        let items = completion(&state, uri, Position::new(1, 1));

        let double_item = items
            .iter()
            .find(|i| completion_insert_name(i) == "double")
            .expect("double should appear in completion");
        assert_eq!(double_item.label, "double");
        assert_eq!(double_item.insert_text.as_deref(), Some("double"));
        assert_eq!(double_item.detail.as_deref(), Some("fn(f64) -> f64"));
        assert_eq!(
            double_item
                .label_details
                .as_ref()
                .and_then(|details| details.detail.as_deref()),
            Some(": fn(f64) -> f64")
        );
    }

    #[test]
    fn completion_keeps_type_detail_during_partial_identifier_edit() {
        let project = TestProject::new("completion-partial-identifier-type-detail");
        let source = "fn double(x: f64) -> f64 { x + x }\ndo\n";
        let (state, uri) = project.open("main.hern", source);

        let items = completion(&state, uri, Position::new(1, 2));

        let double_item = items
            .iter()
            .find(|i| completion_insert_name(i) == "double")
            .expect("double should appear while a partial identifier is being typed");
        assert_eq!(double_item.label, "double");
        assert_eq!(double_item.detail.as_deref(), Some("fn(f64) -> f64"));
        assert_eq!(
            double_item.text_edit.as_ref(),
            Some(&CompletionTextEdit::Edit(TextEdit {
                range: Range::new(Position::new(1, 0), Position::new(1, 2)),
                new_text: "double".to_string(),
            }))
        );
    }

    #[test]
    fn completion_provides_type_detail_for_local_and_parameter() {
        let project = TestProject::new("completion-local-param-detail");
        let source = "fn run(x) { let local = x + 1; local }\nrun(1)\n";
        let (state, uri) = project.open("main.hern", source);

        let items = completion(&state, uri, Position::new(0, 34));

        let x_item = items
            .iter()
            .find(|i| completion_insert_name(i) == "x")
            .expect("parameter should appear in completion");
        let local_item = items
            .iter()
            .find(|i| completion_insert_name(i) == "local")
            .expect("local should appear in completion");

        assert_eq!(x_item.detail.as_deref(), Some("f64"));
        assert_eq!(local_item.detail.as_deref(), Some("f64"));
        assert_eq!(
            x_item
                .label_details
                .as_ref()
                .and_then(|details| details.detail.as_deref()),
            Some(": f64")
        );
        assert_eq!(
            local_item
                .label_details
                .as_ref()
                .and_then(|details| details.detail.as_deref()),
            Some(": f64")
        );
    }

    #[test]
    fn completion_formats_constrained_type_detail() {
        let project = TestProject::new("completion-constrained-detail");
        let source = concat!(
            "fn sum(xs) {\n",
            "  let mut acc = 0;\n",
            "  for x in xs { acc = acc + x; }\n",
            "  acc\n",
            "}\n",
            "\n",
        );
        let (state, uri) = project.open("main.hern", source);

        let items = completion(&state, uri, Position::new(5, 0));

        let sum_item = items
            .iter()
            .find(|i| completion_insert_name(i) == "sum")
            .expect("sum should appear in completion");
        assert_eq!(sum_item.detail.as_deref(), Some("fn('a(f64)) -> f64"));
        assert_eq!(
            sum_item
                .label_details
                .as_ref()
                .and_then(|details| details.detail.as_deref()),
            Some(": fn('a(f64)) -> f64")
        );
    }

    #[test]
    fn completion_parse_only_fallback_returns_names_on_type_error() {
        let project = TestProject::new("completion-parse-fallback");
        let source = "let bad: bool = 1;\nfn helper() { 1 }\nhelper()\n";
        let (state, uri) = project.open("main.hern", source);

        let items = completion(&state, uri, Position::new(2, 1));

        let names: Vec<_> = items.iter().map(completion_insert_name).collect();
        assert!(
            names.contains(&"helper"),
            "helper should appear even when inference fails"
        );
        assert!(
            names.contains(&"bad"),
            "bad should appear even when inference fails"
        );
    }

    #[test]
    fn completion_recovering_fallback_returns_names_on_syntax_error() {
        let project = TestProject::new("completion-recovering-fallback");
        let on_disk = "fn helper() { 1 }\nhelper()\n";
        let uri = project.write("main.hern", on_disk);

        let mid_edit = "fn helper() { 1 }\nfn broken(\n";
        let state = state_with_document(uri.clone(), mid_edit.to_string());

        let items = completion(&state, uri, Position::new(0, 5));

        let names: Vec<_> = items.iter().map(completion_insert_name).collect();
        assert!(
            names.contains(&"helper"),
            "helper should appear even when overlay has a syntax error; got {:?}",
            names
        );
    }

    #[test]
    fn completion_in_gap_between_let_and_for_shows_parameter_and_local() {
        let project = TestProject::new("completion-gap-let-for");
        let source = concat!(
            "fn sum(steps) {\n",
            "  let mut total = 0;\n",
            "\n",
            "  for step in steps {\n",
            "    total = total + step;\n",
            "  }\n",
            "\n",
            "  total\n",
            "}\n",
        );
        let uri = project.write("main.hern", source);

        let with_edit = concat!(
            "fn sum(steps) {\n",
            "  let mut total = 0;\n",
            "  t\n",
            "  for step in steps {\n",
            "    total = total + step;\n",
            "  }\n",
            "\n",
            "  total\n",
            "}\n",
        );
        let state = state_with_document(uri.clone(), with_edit.to_string());

        let items = completion(&state, uri, Position::new(2, 3));
        let names: Vec<_> = items.iter().map(completion_insert_name).collect();

        assert!(
            names.contains(&"total"),
            "`total` should be visible at the gap; got {:?}",
            names
        );
        assert!(
            names.contains(&"steps"),
            "`steps` should be visible at the gap; got {:?}",
            names
        );
    }

    // --- Workspace tracking tests ---

    #[test]
    fn entries_affected_excludes_dep_only_uri_from_self() {
        let ImportFixture {
            mut state,
            entry_uri,
            dep_uri,
        } = import_fixture(
            "affected-dep-only",
            "let dep = import \"dep\";\ndep.value\n",
            "#{ value: 1 }\n",
        );
        diagnostics_for_document(&mut state, &entry_uri);

        let affected = state.entries_affected_by_document(&dep_uri);
        assert!(
            affected.contains(&entry_uri),
            "owning entry should be in affected set"
        );
        assert!(
            !affected.contains(&dep_uri),
            "dep-only URI should not be in its own affected set"
        );
    }

    #[test]
    fn entries_affected_includes_open_entry_uri_itself() {
        let project = TestProject::new("affected-open-entry");
        let (state, uri) = project.open("main.hern", "let value = 1;\n");

        let affected = state.entries_affected_by_document(&uri);
        assert!(
            affected.contains(&uri),
            "open entry URI should be in its own affected set"
        );
    }

    #[test]
    fn closing_dep_only_does_not_clear_entry_diagnostics_for_dep() {
        let ImportFixture {
            mut state,
            entry_uri,
            dep_uri,
        } = import_fixture(
            "close-dep-only-diagnostics",
            "let dep = import \"dep\";\ndep.value\n",
            "#{ value: 1 }\n",
        );
        assert!(diagnostics_for_document(&mut state, &entry_uri)[&entry_uri].is_empty());

        state.set_document(dep_uri.clone(), "let broken = ;\n".to_string(), 1);
        let dep_diags = diagnostics_for_document(&mut state, &entry_uri);
        assert_eq!(
            dep_diags
                .get(&dep_uri)
                .expect("dep should have errors")
                .len(),
            1,
            "dep should have one error before close"
        );

        assert!(
            !state.is_open_entry(&dep_uri),
            "dep added via set_document only should not be an open entry"
        );

        state.unmark_open_entry(&dep_uri);
        state.remove_document(&dep_uri);

        assert!(
            state.entry_dependencies.contains_key(&entry_uri),
            "entry's dependency tracking should be intact after dep-only close"
        );
    }

    #[test]
    fn closing_entry_clears_its_own_diagnostics_but_not_other_entry_contributions() {
        // When entry_a is closed, its diagnostics_by_entry slot should be removable
        // without affecting entry_b's contributions to the same dep.
        let dep = uri("file:///workspace/dep.hern");
        let entry_a = uri("file:///workspace/a.hern");
        let entry_b = uri("file:///workspace/b.hern");

        let mut state = ServerState::new().expect("server state should initialize");
        state.open_entry_uris.insert(entry_a.clone());
        state.open_entry_uris.insert(entry_b.clone());
        state.diagnostics_by_entry.insert(
            entry_a.clone(),
            HashMap::from([(dep.clone(), vec![diagnostic("error from a")])]),
        );
        state.diagnostics_by_entry.insert(
            entry_b.clone(),
            HashMap::from([(dep.clone(), vec![diagnostic("error from b")])]),
        );
        state.entry_dependencies.insert(
            entry_a.clone(),
            HashSet::from([entry_a.clone(), dep.clone()]),
        );

        // Closing entry_a: remove its slot. entry_b's contribution should survive.
        state.diagnostics_by_entry.remove(&entry_a);
        state.remove_entry_tracking(&entry_a);
        state.unmark_open_entry(&entry_a);

        let combined = combined_diagnostics_for_uri(&state, &dep);
        assert_eq!(combined.len(), 1);
        assert_eq!(combined[0].message, "error from b");
    }

    #[test]
    fn entry_stops_importing_dep_stale_diagnostics_disappear() {
        let ImportFixture {
            mut state,
            entry_uri,
            dep_uri,
        } = import_fixture(
            "stale-dep-diag",
            "let dep = import \"dep\";\ndep.value\n",
            "let broken = ;\n",
        );

        let first = diagnostics_for_document(&mut state, &entry_uri);
        assert!(
            first.get(&dep_uri).is_some_and(|d| !d.is_empty()),
            "dep errors should appear initially"
        );

        state.set_document(entry_uri.clone(), "let value = 42;\n".to_string(), 1);
        let second = diagnostics_for_document(&mut state, &entry_uri);

        assert!(
            second.get(&dep_uri).is_none_or(|d| d.is_empty()),
            "stale dep diagnostics should be gone after entry stops importing dep"
        );
    }

    #[test]
    fn imported_dep_edit_updates_hover_after_revalidation() {
        let ImportFixture {
            mut state,
            entry_uri,
            dep_uri,
        } = import_fixture(
            "dep-edit-hover",
            "let dep = import \"dep\";\ndep.value\n",
            "#{ value: 1 }\n",
        );

        assert!(diagnostics_for_document(&mut state, &entry_uri)[&entry_uri].is_empty());
        assert!(cached_analysis(&state, &entry_uri).is_some());

        state.set_document(dep_uri, "#{ value: \"hello\" }\n".to_string(), 1);
        assert!(cached_analysis(&state, &entry_uri).is_none());

        assert!(diagnostics_for_document(&mut state, &entry_uri)[&entry_uri].is_empty());

        let info = hover(&state, entry_uri, Position::new(1, 5)).expect("hover should resolve");
        assert_eq!(
            hover_text(info),
            "string",
            "hover should reflect the updated dep type"
        );
    }

    #[test]
    fn imported_dep_edit_updates_definition_after_revalidation() {
        let ImportFixture {
            mut state,
            entry_uri,
            dep_uri,
        } = import_fixture(
            "dep-edit-definition",
            "let dep = import \"dep\";\ndep.value()\n",
            "fn value() { 1 }\n#{ value: value }\n",
        );

        assert!(diagnostics_for_document(&mut state, &entry_uri)[&entry_uri].is_empty());

        state.set_document(
            dep_uri.clone(),
            "fn value() { \"hello\" }\n#{ value: value }\n".to_string(),
            1,
        );
        assert!(diagnostics_for_document(&mut state, &entry_uri)[&entry_uri].is_empty());

        let loc = definition(&state, entry_uri, Position::new(1, 5))
            .expect("definition should resolve after dep overlay");
        assert_eq!(
            loc.uri, dep_uri,
            "definition should point into the dep module"
        );
    }
}
