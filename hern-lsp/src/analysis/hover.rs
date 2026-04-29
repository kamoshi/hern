use super::state::{ServerState, cached_analysis};
use super::uri::uri_to_path;
use super::workspace::load_workspace_graphs;
use hern_core::analysis::hover_at;
use hern_core::ast::{
    BinOp, Expr, ExprKind, Fixity, ImplMethod, Pattern, Program, SourcePosition, SourceSpan, Stmt,
    TraitMethod,
};
use hern_core::module::{GraphInference, ModuleGraph};
use hern_core::source_index::{Definition, DefinitionKind, ImportMemberReference, index_program};
use hern_core::types::infer::{TypeEnv, VariantEnv};
use hern_core::types::{
    Scheme, TraitConstraint, Ty, TyVar, display_ty_with_var_names, free_type_vars_in_display_order,
    type_var_name,
};
use lsp_types::{Hover, HoverContents, MarkupContent, MarkupKind, Position};
use std::collections::HashMap;

pub(crate) fn hover(state: &ServerState, uri: lsp_types::Uri, position: Position) -> Option<Hover> {
    let path = uri_to_path(&uri)?;
    let fallback;
    let (graph, inference) = if let Some(analysis) = cached_analysis(state, &uri) {
        (&analysis.graph, &analysis.inference)
    } else {
        fallback = load_workspace_graphs(state, &uri)?;
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
    if let Some(contents) = operator_hover(graph, inference, module_name, program, position) {
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
        let import_alias = index
            .definitions
            .iter()
            .find(|definition| definition.symbol == reference.import_symbol)
            .map(|definition| definition.name.as_str());
        return imported_member_hover_text(graph, inference, reference, import_alias);
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

struct OperatorUse<'a> {
    name: &'a str,
}

fn operator_hover(
    graph: &ModuleGraph,
    inference: &GraphInference,
    module_name: &str,
    program: &Program,
    position: SourcePosition,
) -> Option<String> {
    let operator = operator_use_at(program, position)?;
    operator_definition_hover_text(
        program,
        inference.env_for_module(module_name),
        inference.definition_schemes_for_module(module_name),
        operator.name,
    )
    .or_else(|| operator_definition_hover_text(&graph.prelude, None, None, operator.name))
}

fn operator_use_at(program: &Program, position: SourcePosition) -> Option<OperatorUse<'_>> {
    program
        .stmts
        .iter()
        .find_map(|stmt| operator_use_in_stmt(stmt, position))
}

fn operator_use_in_stmt(stmt: &Stmt, position: SourcePosition) -> Option<OperatorUse<'_>> {
    match stmt {
        Stmt::Let { value, .. } | Stmt::Expr(value) => operator_use_in_expr(value, position),
        Stmt::Fn { body, .. } | Stmt::Op { body, .. } => operator_use_in_expr(body, position),
        Stmt::Impl(impl_def) => impl_def
            .methods
            .iter()
            .find_map(|method| operator_use_in_expr(&method.body, position)),
        Stmt::Trait(_) | Stmt::Type(_) | Stmt::TypeAlias { .. } | Stmt::Extern { .. } => None,
    }
}

fn operator_use_in_expr(expr: &Expr, position: SourcePosition) -> Option<OperatorUse<'_>> {
    if !contains(expr.span, position) {
        return None;
    }

    match &expr.kind {
        ExprKind::Binary {
            lhs,
            op,
            op_span,
            rhs,
            ..
        } => {
            if contains(*op_span, position)
                && let BinOp::Custom(name) = op
            {
                return Some(OperatorUse { name });
            }
            operator_use_in_expr(lhs, position).or_else(|| operator_use_in_expr(rhs, position))
        }
        ExprKind::Not(inner)
        | ExprKind::Loop(inner)
        | ExprKind::Break(Some(inner))
        | ExprKind::Return(Some(inner))
        | ExprKind::FieldAccess { expr: inner, .. }
        | ExprKind::Lambda { body: inner, .. } => operator_use_in_expr(inner, position),
        ExprKind::Assign { target, value } => {
            operator_use_in_expr(target, position).or_else(|| operator_use_in_expr(value, position))
        }
        ExprKind::Call { callee, args, .. } => {
            operator_use_in_expr(callee, position).or_else(|| {
                args.iter()
                    .find_map(|arg| operator_use_in_expr(arg, position))
            })
        }
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
        } => operator_use_in_expr(cond, position)
            .or_else(|| operator_use_in_expr(then_branch, position))
            .or_else(|| operator_use_in_expr(else_branch, position)),
        ExprKind::Match { scrutinee, arms } => {
            operator_use_in_expr(scrutinee, position).or_else(|| {
                arms.iter()
                    .find_map(|(_, body)| operator_use_in_expr(body, position))
            })
        }
        ExprKind::Block { stmts, final_expr } => stmts
            .iter()
            .find_map(|stmt| operator_use_in_stmt(stmt, position))
            .or_else(|| {
                final_expr
                    .as_deref()
                    .and_then(|expr| operator_use_in_expr(expr, position))
            }),
        ExprKind::Tuple(items) | ExprKind::Array(items) => items
            .iter()
            .find_map(|item| operator_use_in_expr(item, position)),
        ExprKind::Record(fields) => fields
            .iter()
            .find_map(|(_, value)| operator_use_in_expr(value, position)),
        ExprKind::For { iterable, body, .. } => operator_use_in_expr(iterable, position)
            .or_else(|| operator_use_in_expr(body, position)),
        ExprKind::Break(None)
        | ExprKind::Continue
        | ExprKind::Return(None)
        | ExprKind::Number(_)
        | ExprKind::StringLit(_)
        | ExprKind::Bool(_)
        | ExprKind::Ident(_)
        | ExprKind::Import(_)
        | ExprKind::Unit => None,
    }
}

fn operator_definition_hover_text(
    program: &Program,
    env: Option<&TypeEnv>,
    definition_schemes: Option<&HashMap<SourceSpan, Scheme>>,
    operator: &str,
) -> Option<String> {
    program.stmts.iter().find_map(|stmt| match stmt {
        Stmt::Op {
            name,
            name_span,
            fixity,
            prec,
            ..
        } if name == operator => {
            let ty = definition_schemes
                .and_then(|schemes| schemes.get(name_span))
                .map(hover_scheme_to_string)
                .or_else(|| {
                    env.and_then(|env| env.get(name))
                        .map(|info| hover_scheme_to_string(&info.scheme))
                })?;
            Some(with_fixity_line(ty, *fixity, *prec))
        }
        Stmt::Trait(trait_def) => trait_def
            .methods
            .iter()
            .find(|method| method.name == operator)
            .and_then(trait_operator_hover_text),
        _ => None,
    })
}

fn operator_definition_fixity(program: &Program, span: SourceSpan) -> Option<(Fixity, u8)> {
    program.stmts.iter().find_map(|stmt| match stmt {
        Stmt::Op {
            name_span,
            fixity,
            prec,
            ..
        } if *name_span == span => Some((*fixity, *prec)),
        _ => None,
    })
}

fn trait_operator_hover_text(method: &TraitMethod) -> Option<String> {
    let (fixity, prec) = method.fixity?;
    let params = method
        .params
        .iter()
        .map(|(_, ty)| ast_type_to_string(ty))
        .collect::<Vec<_>>()
        .join(", ");
    let ty = format!("fn({}) -> {}", params, ast_type_to_string(&method.ret_type));
    Some(with_fixity_line(ty, fixity, prec))
}

fn with_fixity_line(ty: String, fixity: Fixity, prec: u8) -> String {
    format!("{ty}\n{} {prec}", fixity_keyword(fixity))
}

fn fixity_keyword(fixity: Fixity) -> &'static str {
    match fixity {
        Fixity::Left => "infixl",
        Fixity::Right => "infixr",
        Fixity::Non => "infix",
    }
}

fn contains(span: SourceSpan, pos: SourcePosition) -> bool {
    let start = (span.start_line, span.start_col);
    let end = (span.end_line, span.end_col);
    let cursor = (pos.line, pos.col);
    cursor >= start && cursor < end
}

/// Display a bare `Ty` with normalized type variable names.
///
/// Unlike `ty.to_string()`, this wraps the type in a `Scheme` so that internal
/// type variable IDs (e.g. `'70`) are renamed to human-readable names (`'a`, `'b`, …).
pub(super) fn ty_to_display_string(ty: &Ty) -> String {
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

pub(super) fn completion_ty_to_display_string(ty: &Ty) -> String {
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

pub(super) fn hover_scheme_to_string(scheme: &Scheme) -> String {
    scheme_to_display_string(scheme, true)
}

pub(super) fn completion_scheme_to_string(scheme: &Scheme) -> String {
    scheme_to_display_string(scheme, false)
}

fn scheme_to_display_string(scheme: &Scheme, include_constraints: bool) -> String {
    let names = type_var_names(scheme);
    let mut out = display_ty_body_for_lsp(&scheme.ty, &names);
    if include_constraints {
        let constraints = constraints_by_var(scheme, &names);
        if !constraints.is_empty() {
            out.push_str("\n");
            for (name, traits) in constraints {
                out.push_str(&format!("\n'{}: {}", name, traits.join(" + ")));
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
    let signature = format!(
        "fn {}({}) -> {}",
        method.name,
        params,
        ast_type_to_string(&method.ret_type)
    );
    method
        .fixity
        .map(|(fixity, prec)| with_fixity_line(signature.clone(), fixity, prec))
        .unwrap_or(signature)
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
    import_alias: Option<&str>,
) -> Option<String> {
    // Primary path: look up the field from the module's concrete export type.
    // This is correct for all export shapes, including aliased names.
    if let Some(Ty::Record(row)) = inference.import_types.get(&reference.module_name) {
        if let Some((_, field_ty)) = row.fields.iter().find(|(f, _)| f == &reference.member_name) {
            return Some(imported_member_display(
                import_alias,
                reference,
                ty_to_display_string(field_ty),
            ));
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
    .map(|text| imported_member_display(import_alias, reference, text))
}

fn imported_member_display(
    import_alias: Option<&str>,
    reference: &ImportMemberReference,
    text: String,
) -> String {
    let module = import_alias.unwrap_or(&reference.module_name);
    format!("{}.{}: {}", module, reference.member_name, text)
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
        let text = hover_scheme_to_string(scheme);
        return Some(
            operator_definition_fixity(program, definition.location.span)
                .map(|(fixity, prec)| with_fixity_line(text.clone(), fixity, prec))
                .unwrap_or(text),
        );
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
        ExprKind::Lambda { params, body, .. } => {
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
