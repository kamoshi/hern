use super::snapshot::{SnapshotMode, analysis_snapshot};
use super::state::ServerState;
use super::uri::{source_span_to_range, uri_to_path};
use super::workspace::document_source;
use hern_core::analysis::{
    PreludeAnalysis, analyze_prelude_source, hover_at, is_synthetic_interpolation_concat,
};
use hern_core::ast::{
    BinOp, Expr, ExprKind, Fixity, ImplMethod, InherentMethod, Param, Pattern, Program,
    SourcePosition, SourceSpan, Stmt, TraitDef, TraitMethod, byte_to_source_position,
    source_position_to_byte, walk_program_exprs,
};
use hern_core::module::{GraphInference, ModuleEnv, ModuleGraph};
use hern_core::source_index::{Definition, DefinitionKind, ImportMemberReference, index_program};
use hern_core::types::infer::{TypeEnv, VariantEnv};
use hern_core::types::{
    BindingCapabilities, Scheme, TraitConstraint, Ty, TyVar, determinant_indexes_are_prefix,
    display_ty_with_var_names, free_type_vars_in_display_order, trait_impl_arg_keys_from_ast,
    trait_impl_dict_name_from_keys, type_var_name,
};
use lsp_types::{Hover, HoverContents, MarkupContent, MarkupKind, Position};
use std::collections::HashMap;
use std::path::Path;

pub(crate) fn hover(state: &ServerState, uri: lsp_types::Uri, position: Position) -> Option<Hover> {
    let path = uri_to_path(&uri)?;
    if is_std_prelude_path(&path) {
        return prelude_hover(state, &uri, position);
    }
    let snapshot = analysis_snapshot(state, &uri, SnapshotMode::RequireTyped)?;
    let graph = snapshot.graph();
    let inference = snapshot.inference()?;
    let (module_name, program) = snapshot.module()?;
    let source = document_source(state, &uri)?;
    let expr_types = inference.expr_types_for_module(module_name)?;
    let symbol_types = inference.symbol_types_for_module(module_name)?;
    let binding_capabilities = inference.binding_capabilities_for_module(module_name);
    let callable_capabilities = inference.callable_capabilities_for_module(module_name);
    let position = SourcePosition {
        line: position.line as usize + 1,
        col: position.character as usize + 1,
    };
    let markdown = state.supports_markdown_hover;
    if let Some(info) = callable_keyword_hover(
        program,
        &source,
        expr_types,
        inference.definition_schemes_for_module(module_name),
        inference.env_for_module(module_name),
        position,
    ) {
        return Some(type_hover_with_span(info.contents, markdown, info.span));
    }
    if let Some(contents) = symbol_hover(graph, inference, module_name, program, position) {
        return Some(type_hover(contents, markdown));
    }
    if let Some(contents) = operator_hover(graph, inference, module_name, program, position) {
        return Some(type_hover(contents, markdown));
    }
    // Hover for `TraitName::method(...)` call sites: the trait name and the method field.
    if let Some(contents) = trait_access_hover(
        program,
        inference.module_env_for_module(module_name),
        position,
    ) {
        return Some(type_hover(contents, markdown));
    }
    let info = hover_at(program, expr_types, symbol_types, position)?;
    let place_mutable = binding_capabilities
        .and_then(|capabilities| capabilities.get(&info.span))
        .is_some_and(|capabilities| capabilities.place_mutable);
    if callable_capabilities
        .and_then(|caps| caps.get(&info.node_id))
        .is_some()
    {
        return Some(type_hover_with_span(
            ty_to_display_string(&info.ty),
            markdown,
            info.span,
        ));
    }
    Some(type_hover_with_span(
        ty_to_display_string_with_place_mutability(&info.ty, place_mutable),
        markdown,
        info.span,
    ))
}

fn prelude_hover(state: &ServerState, uri: &lsp_types::Uri, position: Position) -> Option<Hover> {
    let source = document_source(state, uri)?;
    let prelude = match analyze_prelude_source(&source) {
        Ok(prelude) => prelude,
        Err(_) => state.prelude.clone(),
    };
    prelude_hover_from_analysis(state, &prelude, &source, position)
}

fn prelude_hover_from_analysis(
    state: &ServerState,
    prelude: &PreludeAnalysis,
    source: &str,
    position: Position,
) -> Option<Hover> {
    let position = SourcePosition {
        line: position.line as usize + 1,
        col: position.character as usize + 1,
    };
    let markdown = state.supports_markdown_hover;
    let index = index_program(&prelude.program);
    if let Some(info) = callable_keyword_hover(
        &prelude.program,
        &source,
        &prelude.inference.expr_types,
        Some(&prelude.inference.definition_schemes),
        Some(&prelude.inference.env),
        position,
    ) {
        return Some(type_hover_with_span(info.contents, markdown, info.span));
    }
    if let Some(definition) = index.definition_at(position)
        && let Some(contents) = definition_hover_text(
            definition,
            Some(&prelude.inference.env),
            Some(&prelude.inference.expr_types),
            Some(&prelude.inference.binding_types),
            Some(&prelude.inference.definition_schemes),
            Some(&prelude.inference.binding_capabilities),
            Some(&prelude.inference.variant_env),
            &prelude.program,
        )
    {
        return Some(type_hover(contents, markdown));
    }
    if let Some(operator) = operator_use_at(&prelude.program, position)
        && let Some(contents) = operator_definition_hover_text(
            &prelude.program,
            Some(&prelude.inference.env),
            Some(&prelude.inference.definition_schemes),
            &operator.name,
            operator.arity,
        )
    {
        return Some(type_hover(contents, markdown));
    }
    let info = hover_at(
        &prelude.program,
        &prelude.inference.expr_types,
        &prelude.inference.symbol_types,
        position,
    )?;
    let place_mutable = prelude
        .inference
        .binding_capabilities
        .get(&info.span)
        .is_some_and(|capabilities| capabilities.place_mutable);
    if prelude
        .inference
        .callable_capabilities
        .contains_key(&info.node_id)
    {
        return Some(type_hover_with_span(
            ty_to_display_string(&info.ty),
            markdown,
            info.span,
        ));
    }
    Some(type_hover_with_span(
        ty_to_display_string_with_place_mutability(&info.ty, place_mutable),
        markdown,
        info.span,
    ))
}

fn is_std_prelude_path(path: &Path) -> bool {
    path.file_name().is_some_and(|name| name == "prelude.hern")
        && path
            .parent()
            .and_then(Path::file_name)
            .is_some_and(|name| name == "std")
}

/// Wrap a type string for display in a hover response.
///
/// When `markdown` is true (client advertised markdown hover support), the type is
/// wrapped in a fenced `hern` code block so editors can syntax-highlight it.
/// When false, a plain-text response is returned for compatibility with older clients.
fn type_hover(ty: String, markdown: bool) -> Hover {
    type_hover_inner(ty, markdown, None)
}

fn type_hover_with_span(ty: String, markdown: bool, span: SourceSpan) -> Hover {
    type_hover_inner(ty, markdown, Some(span))
}

fn type_hover_inner(ty: String, markdown: bool, span: Option<SourceSpan>) -> Hover {
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
        range: span.map(source_span_to_range),
    }
}

struct CallableKeywordHover {
    span: SourceSpan,
    contents: String,
}

fn callable_keyword_hover(
    program: &Program,
    source: &str,
    expr_types: &HashMap<hern_core::ast::NodeId, Ty>,
    definition_schemes: Option<&HashMap<SourceSpan, Scheme>>,
    env: Option<&TypeEnv>,
    position: SourcePosition,
) -> Option<CallableKeywordHover> {
    let mut best = None;
    let context = CallableKeywordHoverContext {
        source,
        expr_types,
        definition_schemes,
        env,
        position,
    };
    for stmt in &program.stmts {
        callable_keyword_hover_in_stmt(stmt, &context, &mut best);
    }
    best
}

struct CallableKeywordHoverContext<'a> {
    source: &'a str,
    expr_types: &'a HashMap<hern_core::ast::NodeId, Ty>,
    definition_schemes: Option<&'a HashMap<SourceSpan, Scheme>>,
    env: Option<&'a TypeEnv>,
    position: SourcePosition,
}

fn callable_keyword_hover_in_stmt(
    stmt: &Stmt,
    context: &CallableKeywordHoverContext<'_>,
    best: &mut Option<CallableKeywordHover>,
) {
    match stmt {
        Stmt::Fn {
            span,
            name,
            name_span,
            body,
            ..
        } => {
            if let Some(contents) = callable_scheme_text(name, *name_span, context) {
                consider_callable_keyword(context, best, *span, Some(*name_span), contents);
            }
            callable_keyword_hover_in_expr(body, context, best);
        }
        Stmt::Op {
            span,
            name,
            name_span,
            fixity,
            prec,
            body,
            ..
        } => {
            if let Some(contents) = callable_scheme_text(name, *name_span, context)
                .map(|ty| with_fixity_line(ty, *fixity, *prec))
            {
                consider_callable_keyword(context, best, *span, Some(*name_span), contents);
            }
            callable_keyword_hover_in_expr(body, context, best);
        }
        Stmt::Let { value, .. } | Stmt::Expr(value) => {
            callable_keyword_hover_in_expr(value, context, best);
        }
        Stmt::Trait(trait_def) => {
            for method in &trait_def.methods {
                consider_callable_keyword(
                    context,
                    best,
                    method.span,
                    Some(method.name_span),
                    trait_method_signature(method),
                );
            }
        }
        Stmt::Impl(impl_def) => {
            if impl_def.generated_by.is_some() {
                return;
            }
            for method in &impl_def.methods {
                let contents = context
                    .definition_schemes
                    .and_then(|schemes| schemes.get(&method.name_span))
                    .map(hover_scheme_to_string)
                    .unwrap_or_else(|| impl_method_signature(method));
                consider_callable_keyword(
                    context,
                    best,
                    method.span,
                    Some(method.name_span),
                    contents,
                );
                callable_keyword_hover_in_expr(&method.body, context, best);
            }
        }
        Stmt::InherentImpl(impl_def) => {
            for method in &impl_def.methods {
                let contents = context
                    .definition_schemes
                    .and_then(|schemes| schemes.get(&method.name_span))
                    .map(hover_scheme_to_string)
                    .unwrap_or_else(|| inherent_method_signature(method));
                consider_callable_keyword(
                    context,
                    best,
                    method.span,
                    Some(method.name_span),
                    contents,
                );
                callable_keyword_hover_in_expr(&method.body, context, best);
            }
        }
        Stmt::TestBlock { stmts, .. } | Stmt::RecBlock { stmts, .. } => {
            for stmt in stmts {
                callable_keyword_hover_in_stmt(stmt, context, best);
            }
        }
        Stmt::Macro(_) | Stmt::Type(_) | Stmt::TypeAlias { .. } | Stmt::Extern { .. } => {}
    }
}

fn callable_keyword_hover_in_expr(
    expr: &Expr,
    context: &CallableKeywordHoverContext<'_>,
    best: &mut Option<CallableKeywordHover>,
) {
    if !contains(expr.span, context.position) {
        return;
    }
    match &expr.kind {
        ExprKind::Lambda { body, .. } => {
            if let Some(ty) = context.expr_types.get(&expr.id) {
                consider_callable_keyword(context, best, expr.span, None, ty_to_display_string(ty));
            }
            callable_keyword_hover_in_expr(body, context, best);
        }
        ExprKind::Grouped(inner)
        | ExprKind::Not(inner)
        | ExprKind::Neg { operand: inner, .. }
        | ExprKind::Loop(inner)
        | ExprKind::Break(Some(inner))
        | ExprKind::Return(Some(inner))
        | ExprKind::FieldAccess { expr: inner, .. } => {
            callable_keyword_hover_in_expr(inner, context, best);
        }
        ExprKind::Assign { target, value } => {
            callable_keyword_hover_in_expr(target, context, best);
            callable_keyword_hover_in_expr(value, context, best);
        }
        ExprKind::Binary { lhs, rhs, .. } => {
            callable_keyword_hover_in_expr(lhs, context, best);
            callable_keyword_hover_in_expr(rhs, context, best);
        }
        ExprKind::Range { start, end, .. } => {
            if let Some(start) = start {
                callable_keyword_hover_in_expr(start, context, best);
            }
            if let Some(end) = end {
                callable_keyword_hover_in_expr(end, context, best);
            }
        }
        ExprKind::Call { callee, args, .. } => {
            callable_keyword_hover_in_expr(callee, context, best);
            for arg in args {
                callable_keyword_hover_in_expr(arg, context, best);
            }
        }
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
        } => {
            callable_keyword_hover_in_expr(cond, context, best);
            callable_keyword_hover_in_expr(then_branch, context, best);
            callable_keyword_hover_in_expr(else_branch, context, best);
        }
        ExprKind::Match { scrutinee, arms } => {
            callable_keyword_hover_in_expr(scrutinee, context, best);
            for (_, body) in arms {
                callable_keyword_hover_in_expr(body, context, best);
            }
        }
        ExprKind::Block { stmts, final_expr } => {
            for stmt in stmts {
                callable_keyword_hover_in_stmt(stmt, context, best);
            }
            if let Some(expr) = final_expr {
                callable_keyword_hover_in_expr(expr, context, best);
            }
        }
        ExprKind::Tuple(items) => {
            for item in items {
                callable_keyword_hover_in_expr(item, context, best);
            }
        }
        ExprKind::Array(entries) => {
            for entry in entries {
                callable_keyword_hover_in_expr(entry.expr(), context, best);
            }
        }
        ExprKind::Record(entries) => {
            for entry in entries {
                callable_keyword_hover_in_expr(entry.expr(), context, best);
            }
        }
        ExprKind::Index { receiver, key, .. } => {
            callable_keyword_hover_in_expr(receiver, context, best);
            callable_keyword_hover_in_expr(key, context, best);
        }
        ExprKind::For { iterable, body, .. } => {
            callable_keyword_hover_in_expr(iterable, context, best);
            callable_keyword_hover_in_expr(body, context, best);
        }
        ExprKind::Number(_)
        | ExprKind::StringLit(_)
        | ExprKind::Bool(_)
        | ExprKind::SyntaxQuote(_)
        | ExprKind::MacroCall { .. }
        | ExprKind::Ident(_)
        | ExprKind::Import(_)
        | ExprKind::Unit
        | ExprKind::Break(None)
        | ExprKind::Continue
        | ExprKind::Return(None)
        | ExprKind::AssociatedAccess { .. } => {}
    }
}

fn callable_scheme_text(
    name: &str,
    name_span: SourceSpan,
    context: &CallableKeywordHoverContext<'_>,
) -> Option<String> {
    context
        .definition_schemes
        .and_then(|schemes| schemes.get(&name_span))
        .map(hover_scheme_to_string)
        .or_else(|| {
            context
                .env
                .and_then(|env| env.get(name))
                .map(|info| hover_scheme_to_string(&info.scheme))
        })
}

fn consider_callable_keyword(
    context: &CallableKeywordHoverContext<'_>,
    best: &mut Option<CallableKeywordHover>,
    callable_span: SourceSpan,
    before_span: Option<SourceSpan>,
    contents: String,
) {
    if fn_keyword_span(context.source, callable_span, before_span)
        .is_some_and(|span| contains(span, context.position))
        && best
            .as_ref()
            .is_none_or(|current| span_len(callable_span) < span_len(current.span))
    {
        *best = Some(CallableKeywordHover {
            span: callable_span,
            contents,
        });
    }
}

fn fn_keyword_span(
    source: &str,
    callable_span: SourceSpan,
    before_span: Option<SourceSpan>,
) -> Option<SourceSpan> {
    let start = source_position_to_byte(
        source,
        SourcePosition {
            line: callable_span.start_line,
            col: callable_span.start_col,
        },
    )?;
    let end = before_span
        .and_then(|span| {
            source_position_to_byte(
                source,
                SourcePosition {
                    line: span.start_line,
                    col: span.start_col,
                },
            )
        })
        .or_else(|| {
            source_position_to_byte(
                source,
                SourcePosition {
                    line: callable_span.end_line,
                    col: callable_span.end_col,
                },
            )
        })?;
    let search = source.get(start..end)?;
    let relative = find_keyword(search, "fn")?;
    let keyword_start = start + relative;
    let keyword_end = keyword_start + "fn".len();
    Some(SourceSpan {
        start_line: byte_to_source_position(source, keyword_start)?.line,
        start_col: byte_to_source_position(source, keyword_start)?.col,
        end_line: byte_to_source_position(source, keyword_end)?.line,
        end_col: byte_to_source_position(source, keyword_end)?.col,
    })
}

fn find_keyword(source: &str, keyword: &str) -> Option<usize> {
    let mut offset = 0;
    while let Some(relative) = source[offset..].find(keyword) {
        let start = offset + relative;
        let end = start + keyword.len();
        let before = source[..start].chars().next_back();
        let after = source[end..].chars().next();
        if !before.is_some_and(is_identifier_char) && !after.is_some_and(is_identifier_char) {
            return Some(start);
        }
        offset = end;
    }
    None
}

fn is_identifier_char(ch: char) -> bool {
    ch.is_ascii_alphanumeric() || ch == '_'
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
        inference.binding_capabilities_for_module(module_name),
        inference.variant_env_for_module(module_name),
        program,
    )
}

// ── Trait access hover ────────────────────────────────────────────────────────

/// Returns hover text when the cursor is on the trait name or method field in
/// an explicit `TraitName::method(...)` call expression.
fn trait_access_hover(
    program: &Program,
    module_env: Option<&ModuleEnv>,
    position: SourcePosition,
) -> Option<String> {
    let module_env = module_env?;
    let mut hover = None;
    walk_program_exprs(program, &mut |expr| {
        if hover.is_some() || !contains(expr.span, position) {
            return;
        }
        if let ExprKind::AssociatedAccess {
            target: hern_core::ast::Type::Ident(trait_name),
            target_span,
            member,
            member_span,
            ..
        } = &expr.kind
            && !is_synthetic_interpolation_tostring(trait_name, *target_span, member, *member_span)
            && let Some(trait_def) = module_env.trait_def(trait_name)
        {
            if contains(*target_span, position) {
                hover = Some(format!(
                    "trait {} {}",
                    trait_def.name,
                    trait_def.params.join(" ")
                ));
            } else if contains(*member_span, position)
                && let Some(method) = trait_def.methods.iter().find(|m| m.name == *member)
            {
                hover = Some(trait_method_signature(method));
            }
        }
    });
    hover
}

fn is_synthetic_interpolation_tostring(
    trait_name: &str,
    target_span: SourceSpan,
    member: &str,
    member_span: SourceSpan,
) -> bool {
    // Interpolation holes lower through synthetic ToString::to_string calls.
    // The parser gives the target/member the same non-user-visible span.
    trait_name == "ToString" && member == "to_string" && target_span == member_span
}

// ── Operator hover ────────────────────────────────────────────────────────────

struct OperatorUse {
    name: String,
    arity: usize,
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
        &operator.name,
        operator.arity,
    )
    .or_else(|| {
        operator_definition_hover_text(&graph.prelude, None, None, &operator.name, operator.arity)
    })
}

fn operator_use_at(program: &Program, position: SourcePosition) -> Option<OperatorUse> {
    let mut operator = None;
    walk_program_exprs(program, &mut |expr| {
        if operator.is_some() || !contains(expr.span, position) {
            return;
        }
        if let ExprKind::Binary { op, op_span, .. } = &expr.kind
            && contains(*op_span, position)
            && !is_synthetic_interpolation_concat(expr, op, *op_span)
            && let BinOp::Custom(name) = op
        {
            operator = Some(OperatorUse {
                name: name.clone(),
                arity: 2,
            });
        }
        if let ExprKind::Neg { op_span, .. } = &expr.kind
            && contains(*op_span, position)
        {
            operator = Some(OperatorUse {
                name: "-".to_string(),
                arity: 1,
            });
        }
    });
    operator
}

fn operator_definition_hover_text(
    program: &Program,
    env: Option<&TypeEnv>,
    definition_schemes: Option<&HashMap<SourceSpan, Scheme>>,
    operator: &str,
    arity: usize,
) -> Option<String> {
    program.stmts.iter().find_map(|stmt| match stmt {
        Stmt::Op {
            name,
            name_span,
            fixity,
            prec,
            params,
            ..
        } if name == operator && params.len() == arity => {
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
            .find(|method| method.name == operator && method.params.len() == arity)
            .and_then(|method| trait_operator_hover_text(trait_def, method)),
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

fn trait_operator_hover_text(trait_def: &TraitDef, method: &TraitMethod) -> Option<String> {
    let params = method
        .params
        .iter()
        .map(|(_, ty)| ast_type_to_string(ty))
        .collect::<Vec<_>>()
        .join(", ");
    let ty = format!("fn({}) -> {}", params, ast_type_to_string(&method.ret_type));
    let mut result = if let Some((fixity, prec)) = method.fixity {
        with_fixity_line(ty, fixity, prec)
    } else {
        ty
    };
    result.push_str(&format!(
        "\n\n{}: {}",
        trait_def_predicate_for_display(trait_def),
        trait_def.name
    ));
    Some(result)
}

fn trait_def_predicate_for_display(trait_def: &TraitDef) -> String {
    let Some(fundep) = trait_def.fundeps.first() else {
        return trait_def.params.join(" ");
    };
    debug_assert!(
        determinant_indexes_are_prefix(&fundep.determinants),
        "hover display assumes source fundep arrows split a prefix determinant list"
    );
    let mut parts = Vec::new();
    for (index, param) in trait_def.params.iter().enumerate() {
        if index > 0 && index == fundep.determinants.len() {
            parts.push("->".to_string());
        }
        parts.push(param.clone());
    }
    parts.join(" ")
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

fn span_len(span: SourceSpan) -> usize {
    (span.end_line.saturating_sub(span.start_line)) * 100_000
        + span.end_col.saturating_sub(span.start_col)
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

pub(super) fn ty_to_display_string_in_scheme(ty: &Ty, scheme: &Scheme) -> String {
    let names: HashMap<_, _> = free_type_vars_in_display_order(&scheme.ty)
        .into_iter()
        .enumerate()
        .map(|(idx, var)| (var, type_var_name(idx)))
        .collect();
    display_ty_body_for_lsp(ty, &names)
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
        let constraints = constraints_for_display(scheme, &names);
        if !constraints.is_empty() {
            out.push('\n');
            for (predicate, traits) in constraints {
                out.push_str(&format!("\n{}: {}", predicate, traits.join(" + ")));
            }
        }
    }
    out
}

fn display_ty_body_for_lsp(ty: &Ty, names: &HashMap<TyVar, String>) -> String {
    match ty {
        Ty::Qualified(_, inner) => display_ty_body_for_lsp(inner, names),
        Ty::Func(_, _) => display_ty_with_var_names(ty, names),
        _ => display_ty_with_var_names(ty, names),
    }
}

fn ty_to_display_string_with_place_mutability(ty: &Ty, place_mutable: bool) -> String {
    let text = ty_to_display_string(ty);
    if place_mutable {
        format!("mut {text}")
    } else {
        text
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
        for arg in &constraint.args {
            for var in free_type_vars_in_display_order(arg) {
                if !vars.contains(&var) {
                    vars.push(var);
                }
            }
        }
    }

    vars.into_iter()
        .enumerate()
        .map(|(idx, var)| (var, type_var_name(idx)))
        .collect()
}

fn constraints_for_display(
    scheme: &Scheme,
    names: &HashMap<TyVar, String>,
) -> Vec<(String, Vec<String>)> {
    let mut grouped: Vec<(String, Vec<String>)> = Vec::new();
    for constraint in &scheme.constraints {
        let predicate = constraint_predicate_for_display(constraint, names);
        if let Some((_, traits)) = grouped
            .iter_mut()
            .find(|(existing, _)| existing == &predicate)
        {
            if !traits.contains(&constraint.trait_name) {
                traits.push(constraint.trait_name.clone());
            }
        } else {
            grouped.push((predicate, vec![constraint.trait_name.clone()]));
        }
    }
    grouped.sort_by(|(left, _), (right, _)| left.cmp(right));
    grouped
}

fn constraint_predicate_for_display(
    constraint: &TraitConstraint,
    names: &HashMap<TyVar, String>,
) -> String {
    if constraint.args.is_empty() {
        return type_var_for_display(constraint.var, names);
    }
    let dependent_index = first_dependent_index(constraint);
    let mut parts = Vec::new();
    for (index, arg) in constraint.args.iter().enumerate() {
        if index > 0 && dependent_index == Some(index) {
            parts.push("->".to_string());
        }
        parts.push(display_ty_with_var_names(arg, names));
    }
    parts.join(" ")
}

fn first_dependent_index(constraint: &TraitConstraint) -> Option<usize> {
    debug_assert!(
        determinant_indexes_are_prefix(&constraint.determinant_indexes),
        "hover display assumes source fundep arrows split a prefix determinant list"
    );
    if constraint.determinant_indexes.len() < constraint.args.len() {
        Some(constraint.determinant_indexes.len())
    } else {
        None
    }
}

fn type_var_for_display(var: TyVar, names: &HashMap<TyVar, String>) -> String {
    format!(
        "'{}",
        names.get(&var).cloned().unwrap_or_else(|| var.to_string())
    )
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
                "type alias {}{} = {}",
                name,
                type_params_suffix(params),
                ast_type_to_string(ty)
            )),
            _ => None,
        }),
        DefinitionKind::Trait => program.stmts.iter().find_map(|stmt| match stmt {
            Stmt::Trait(trait_def) if trait_def.name_span == definition.location.span => Some(
                format!("trait {} {}", trait_def.name, trait_def.params.join(" ")),
            ),
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
            Stmt::InherentImpl(impl_def) => impl_def
                .methods
                .iter()
                .find(|method| method.name_span == definition.location.span)
                .map(inherent_method_signature),
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
        .map(|param| {
            let pat = pattern_to_string(&param.pat);
            match &param.ty {
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
            ast_type_return_to_string(ret)
        ),
        None => format!("fn {}({})", method.name, params),
    }
}

fn inherent_method_signature(method: &InherentMethod) -> String {
    let params = method
        .params
        .iter()
        .map(|param| {
            let pat = pattern_to_string(&param.pat);
            match &param.ty {
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
            ast_type_return_to_string(ret)
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

pub(super) fn ast_type_to_string(ty: &hern_core::ast::Type) -> String {
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
        Type::Func(params, ret) => {
            let ret_text = ast_type_to_string(&ret.ty);
            format!(
                "fn({}) -> {}{}",
                params
                    .iter()
                    .map(|param| {
                        let text = ast_type_to_string(&param.ty);
                        if param.mut_place {
                            format!("mut {text}")
                        } else {
                            text
                        }
                    })
                    .collect::<Vec<_>>()
                    .join(", "),
                if ret.mut_place { "mut " } else { "" },
                ret_text
            )
        }
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
        Type::Never => "!".to_string(),
        Type::Hole => "*".to_string(),
    }
}

fn ast_type_return_to_string(ret: &hern_core::ast::TypeReturn) -> String {
    let ty = ast_type_to_string(&ret.ty);
    if ret.mut_place {
        format!("mut {ty}")
    } else {
        ty
    }
}

fn pattern_to_string(pat: &Pattern) -> String {
    match pat {
        Pattern::Wildcard => "_".to_string(),
        Pattern::StringLit(value) => format!("{value:?}"),
        Pattern::NumberLit(value) => value.as_lua_source(),
        Pattern::BoolLit(value) => value.to_string(),
        Pattern::IntRange {
            start,
            end,
            inclusive,
        } => {
            let op = if *inclusive { "..=" } else { ".." };
            format!("{start}{op}{end}")
        }
        Pattern::Variable(name, _) => name.clone(),
        Pattern::Constructor { name, binding } => match binding {
            Some(binding) => format!("{name}({})", pattern_to_string(binding)),
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
        Pattern::SyntaxQuote(_) => "`'(...)`".to_string(),
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
    if let Some(scheme) = inference
        .import_schemes
        .get(&reference.module_name)
        .and_then(|members| members.get(&reference.member_name))
    {
        return Some(imported_member_display(
            import_alias,
            reference,
            hover_scheme_to_string(scheme),
        ));
    }

    // Primary path: look up the field from the module's concrete export type.
    // This is correct for all export shapes, including aliased names.
    if let Some(Ty::Record(row)) = inference.import_types.get(&reference.module_name)
        && let Some((_, field_ty)) = row.fields.iter().find(|(f, _)| f == &reference.member_name)
    {
        return Some(imported_member_display(
            import_alias,
            reference,
            ty_to_display_string(field_ty),
        ));
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
        inference.binding_capabilities_for_module(&reference.module_name),
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

#[allow(clippy::too_many_arguments)]
fn definition_hover_text(
    definition: &Definition,
    env: Option<&TypeEnv>,
    expr_types: Option<&HashMap<hern_core::ast::NodeId, Ty>>,
    binding_types: Option<&HashMap<SourceSpan, Ty>>,
    definition_schemes: Option<&HashMap<SourceSpan, Scheme>>,
    binding_capabilities: Option<&HashMap<SourceSpan, BindingCapabilities>>,
    variant_env: Option<&VariantEnv>,
    program: &Program,
) -> Option<String> {
    if let Some(scheme) =
        definition_schemes.and_then(|schemes| schemes.get(&definition.location.span))
    {
        let scheme = env
            .and_then(|env| env.get(&definition.name))
            .map(|info| &info.scheme)
            .unwrap_or(scheme);
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
        let place_mutable = binding_capabilities
            .and_then(|capabilities| capabilities.get(&definition.location.span))
            .is_some_and(|capabilities| capabilities.place_mutable);
        return Some(ty_to_display_string_with_place_mutability(
            ty,
            place_mutable,
        ));
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
    if definition.kind == DefinitionKind::Let
        && let Some(types) = expr_types
        && let Some(ty) = local_pattern_binding_type(
            program,
            &definition.name,
            definition.location.span,
            types,
            binding_types,
            variant_env,
        )
    {
        return Some(ty);
    }

    expr_types
        .and_then(|types| declaration_value_type(program, definition.location.span, types))
        .map(ty_to_display_string)
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
            let dict_key = trait_impl_arg_keys_from_ast(&id.trait_args)
                .ok()
                .map(|targets| trait_impl_dict_name_from_keys(&id.trait_name, &targets))?;
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

/// Find the param in `params` that owns the binding `(param_name, param_span)`, then
/// extract the concrete type of *that binding* from the function's scheme.
///
/// For a top-level `Variable` param the binding type is the whole param type.
/// For a `Record` param the binding type is the type of the matched field.
fn param_type_from_fn_scheme(
    fn_name: &str,
    params: &[Param],
    param_name: &str,
    param_span: SourceSpan,
    env: Option<&TypeEnv>,
    variant_env: Option<&VariantEnv>,
) -> Option<String> {
    let param_idx = params
        .iter()
        .position(|param| pattern_has_binding_at(&param.pat, param_name, param_span))?;
    let param_pat = &params[param_idx].pat;

    let scheme = env.and_then(|e| e.get(fn_name))?;
    let Ty::Func(param_tys, _) = &scheme.scheme.ty else {
        return None;
    };
    let param_ty = &param_tys.get(param_idx)?.ty;

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
        .position(|param| pattern_has_binding_at(&param.pat, param_name, param_span))?;
    let param_pat = &method.params[param_idx].pat;

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
    let param_ty = &param_tys.get(param_idx)?.ty;

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
            if let Some(Some((rest_name, rest_span))) = rest
                && rest_name == target_name
                && *rest_span == target_span
            {
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
            if let Some(Some((rest_name, rest_span))) = rest
                && rest_name == target_name
                && *rest_span == target_span
            {
                return Some(param_ty.clone());
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
            if let Some(binding) = binding {
                let payload_ty = constructor_payload_type(name, param_ty, variant_env)?;
                return extract_binding_type(
                    binding,
                    target_name,
                    target_span,
                    &payload_ty,
                    variant_env,
                );
            }
            None
        }
        Pattern::SyntaxQuote(pattern) => {
            let mut captures = Vec::new();
            hern_core::syntax::collect_syntax_pattern_captures(pattern, &mut captures);
            captures
                .into_iter()
                .find(|capture| capture.name == target_name && capture.span == target_span)
                .map(|capture| {
                    let syntax = Ty::Con("Syntax".to_string());
                    if capture.repeat {
                        Ty::App(Box::new(Ty::Con("Array".to_string())), vec![syntax])
                    } else {
                        syntax
                    }
                })
        }
        // Wildcards have no bindings; any other pattern is unreachable here after
        // the irrefutability check in the type inferencer.
        _ => None,
    }
}

/// Resolve the payload type of a constructor binding such as `Some(x)` or `Err(e)`.
///
/// Uses the variant environment to correctly map type parameters to their instantiated
/// types — for example, `Err(e)` in a `Result(float, string)` correctly yields `string`
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

    if let Some(venv) = variant_env
        && let Some(info) = venv.0.get(constructor)
        && let Some(payload_ty) = &info.payload_ty
    {
        return Some(instantiate_variant_template(
            payload_ty,
            &info.type_param_vars,
            args,
        ));
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
                    Some(hern_core::types::TraitConstraint::unary(
                        var,
                        constraint.trait_name.clone(),
                    ))
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
                .map(|param| hern_core::types::FuncParam {
                    ty: instantiate_variant_template(&param.ty, type_param_vars, args),
                    capability: param.capability,
                })
                .collect(),
            hern_core::types::FuncReturn {
                ty: Box::new(instantiate_variant_template(&ret.ty, type_param_vars, args)),
                capability: ret.capability,
            },
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
        Ty::Int | Ty::Float | Ty::Unit | Ty::Never | Ty::Con(_) => template.clone(),
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
                .position(|param| pattern_has_binding_at(&param.pat, name, param_span))
            {
                // Look up the lambda's Ty::Func from expr_types to get the param type.
                let types = expr_types?;
                let Ty::Func(param_tys, _) = types.get(&expr.id)? else {
                    return None;
                };
                let param_ty = &param_tys.get(idx)?.ty;
                let pat = &params[idx].pat;
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
        ExprKind::Grouped(e)
        | ExprKind::Not(e)
        | ExprKind::Loop(e)
        | ExprKind::Break(Some(e))
        | ExprKind::Return(Some(e))
        | ExprKind::FieldAccess { expr: e, .. } => {
            param_type_in_expr_stmts(e, name, param_span, env, expr_types, variant_env)
        }
        ExprKind::Neg { operand, .. } => {
            param_type_in_expr_stmts(operand, name, param_span, env, expr_types, variant_env)
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
        ExprKind::Range { start, end, .. } => start
            .as_deref()
            .and_then(|expr| {
                param_type_in_expr_stmts(expr, name, param_span, env, expr_types, variant_env)
            })
            .or_else(|| {
                end.as_deref().and_then(|expr| {
                    param_type_in_expr_stmts(expr, name, param_span, env, expr_types, variant_env)
                })
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
        ExprKind::Tuple(items) => items.iter().find_map(|item| {
            param_type_in_expr_stmts(item, name, param_span, env, expr_types, variant_env)
        }),
        ExprKind::Array(entries) => entries.iter().find_map(|e| {
            param_type_in_expr_stmts(e.expr(), name, param_span, env, expr_types, variant_env)
        }),
        ExprKind::Record(entries) => entries.iter().find_map(|e| {
            param_type_in_expr_stmts(e.expr(), name, param_span, env, expr_types, variant_env)
        }),
        ExprKind::For { iterable, body, .. } => {
            param_type_in_expr_stmts(iterable, name, param_span, env, expr_types, variant_env)
                .or_else(|| {
                    param_type_in_expr_stmts(body, name, param_span, env, expr_types, variant_env)
                })
        }
        ExprKind::Index { receiver, key, .. } => {
            param_type_in_expr_stmts(receiver, name, param_span, env, expr_types, variant_env)
                .or_else(|| {
                    param_type_in_expr_stmts(key, name, param_span, env, expr_types, variant_env)
                })
        }
        ExprKind::AssociatedAccess { .. } => None,
        ExprKind::Break(None)
        | ExprKind::Return(None)
        | ExprKind::Continue
        | ExprKind::Number(_)
        | ExprKind::StringLit(_)
        | ExprKind::Bool(_)
        | ExprKind::SyntaxQuote(_)
        | ExprKind::MacroCall { .. }
        | ExprKind::Ident(_)
        | ExprKind::Import(_)
        | ExprKind::Unit => None,
    }
}

fn pattern_has_binding_at(pat: &Pattern, name: &str, span: SourceSpan) -> bool {
    match pat {
        Pattern::Variable(n, s) => n == name && *s == span,
        Pattern::Constructor {
            binding: Some(binding),
            ..
        } => pattern_has_binding_at(binding, name, span),
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
        Pattern::SyntaxQuote(pattern) => {
            let mut captures = Vec::new();
            hern_core::syntax::collect_syntax_pattern_captures(pattern, &mut captures);
            captures
                .iter()
                .any(|capture| capture.name == name && capture.span == span)
        }
        _ => false,
    }
}

/// Returns true if any binding span in `pat` equals `span`.
fn pattern_has_span_at(pat: &Pattern, span: SourceSpan) -> bool {
    match pat {
        Pattern::Variable(_, s) => *s == span,
        Pattern::Constructor {
            binding: Some(binding),
            ..
        } => pattern_has_span_at(binding, span),
        Pattern::Record { fields, rest } => {
            fields.iter().any(|(_, _, s)| *s == span)
                || matches!(rest, Some(Some((_, s))) if *s == span)
        }
        Pattern::List { elements, rest } => {
            elements.iter().any(|elem| pattern_has_span_at(elem, span))
                || matches!(rest, Some(Some((_, s))) if *s == span)
        }
        Pattern::Tuple(elems) => elems.iter().any(|e| pattern_has_span_at(e, span)),
        Pattern::SyntaxQuote(pattern) => {
            let mut captures = Vec::new();
            hern_core::syntax::collect_syntax_pattern_captures(pattern, &mut captures);
            captures.iter().any(|capture| capture.span == span)
        }
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
                && let Some(rhs_ty) = expr_types.get(&value.id)
                && let Some(binding_ty) =
                    extract_binding_type(pat, name, binding_span, rhs_ty, variant_env)
            {
                return Some(ty_to_display_string(&binding_ty));
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
        Stmt::InherentImpl(impl_def) => impl_def.methods.iter().find_map(|method| {
            local_pattern_binding_type_in_expr(
                &method.body,
                name,
                binding_span,
                expr_types,
                variant_env,
            )
        }),
        Stmt::TestBlock { stmts, .. } => stmts.iter().find_map(|stmt| {
            local_pattern_binding_type_in_stmt(stmt, name, binding_span, expr_types, variant_env)
        }),
        Stmt::RecBlock { stmts, .. } => stmts.iter().find_map(|stmt| {
            local_pattern_binding_type_in_stmt(stmt, name, binding_span, expr_types, variant_env)
        }),
        Stmt::Macro(_)
        | Stmt::Trait(_)
        | Stmt::Type(_)
        | Stmt::TypeAlias { .. }
        | Stmt::Extern { .. } => None,
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
            if pattern_has_binding_at(pat, name, binding_span)
                && let Some(iterable_ty) = expr_types.get(&iterable.id)
                && let Some(elem_ty) = iterable_element_type(iterable_ty)
                && let Some(binding_ty) =
                    extract_binding_type(pat, name, binding_span, elem_ty, variant_env)
            {
                return Some(ty_to_display_string(&binding_ty));
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
        ExprKind::Grouped(e)
        | ExprKind::Not(e)
        | ExprKind::Loop(e)
        | ExprKind::Break(Some(e))
        | ExprKind::Return(Some(e))
        | ExprKind::FieldAccess { expr: e, .. }
        | ExprKind::Lambda { body: e, .. } => {
            local_pattern_binding_type_in_expr(e, name, binding_span, expr_types, variant_env)
        }
        ExprKind::Neg { operand, .. } => {
            local_pattern_binding_type_in_expr(operand, name, binding_span, expr_types, variant_env)
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
        ExprKind::Range { start, end, .. } => start
            .as_deref()
            .and_then(|expr| {
                local_pattern_binding_type_in_expr(
                    expr,
                    name,
                    binding_span,
                    expr_types,
                    variant_env,
                )
            })
            .or_else(|| {
                end.as_deref().and_then(|expr| {
                    local_pattern_binding_type_in_expr(
                        expr,
                        name,
                        binding_span,
                        expr_types,
                        variant_env,
                    )
                })
            }),
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
                if pattern_has_binding_at(pat, name, binding_span)
                    && let Some(scrutinee_ty) = expr_types.get(&scrutinee.id)
                    && let Some(binding_ty) =
                        extract_binding_type(pat, name, binding_span, scrutinee_ty, variant_env)
                {
                    return Some(ty_to_display_string(&binding_ty));
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
        ExprKind::Tuple(items) => items.iter().find_map(|item| {
            local_pattern_binding_type_in_expr(item, name, binding_span, expr_types, variant_env)
        }),
        ExprKind::Array(entries) => entries.iter().find_map(|e| {
            local_pattern_binding_type_in_expr(
                e.expr(),
                name,
                binding_span,
                expr_types,
                variant_env,
            )
        }),
        ExprKind::Record(entries) => entries.iter().find_map(|e| {
            local_pattern_binding_type_in_expr(
                e.expr(),
                name,
                binding_span,
                expr_types,
                variant_env,
            )
        }),
        ExprKind::Index { receiver, key, .. } => local_pattern_binding_type_in_expr(
            receiver,
            name,
            binding_span,
            expr_types,
            variant_env,
        )
        .or_else(|| {
            local_pattern_binding_type_in_expr(key, name, binding_span, expr_types, variant_env)
        }),
        ExprKind::AssociatedAccess { .. } => None,
        ExprKind::Break(None)
        | ExprKind::Return(None)
        | ExprKind::Continue
        | ExprKind::Number(_)
        | ExprKind::StringLit(_)
        | ExprKind::Bool(_)
        | ExprKind::SyntaxQuote(_)
        | ExprKind::MacroCall { .. }
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
        Stmt::InherentImpl(impl_def) => impl_def.methods.iter().find_map(|method| {
            (method.name_span == span)
                .then(|| expr_types.get(&method.body.id))
                .flatten()
        }),
        Stmt::TestBlock { stmts, .. } => stmts
            .iter()
            .find_map(|stmt| declaration_value_type_in_stmt(stmt, span, expr_types)),
        Stmt::RecBlock { stmts, .. } => stmts
            .iter()
            .find_map(|stmt| declaration_value_type_in_stmt(stmt, span, expr_types)),
        Stmt::Macro(_)
        | Stmt::Trait(_)
        | Stmt::Type(_)
        | Stmt::TypeAlias { .. }
        | Stmt::Extern { .. } => None,
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
        ExprKind::Grouped(expr)
        | ExprKind::Not(expr)
        | ExprKind::Loop(expr)
        | ExprKind::Break(Some(expr))
        | ExprKind::Return(Some(expr))
        | ExprKind::FieldAccess { expr, .. }
        | ExprKind::Lambda { body: expr, .. } => {
            declaration_value_type_in_expr(expr, span, expr_types)
        }
        ExprKind::Neg { operand, .. } => declaration_value_type_in_expr(operand, span, expr_types),
        ExprKind::Assign { target, value }
        | ExprKind::Binary {
            lhs: target,
            rhs: value,
            ..
        } => declaration_value_type_in_expr(target, span, expr_types)
            .or_else(|| declaration_value_type_in_expr(value, span, expr_types)),
        ExprKind::Range { start, end, .. } => start
            .as_deref()
            .and_then(|expr| declaration_value_type_in_expr(expr, span, expr_types))
            .or_else(|| {
                end.as_deref()
                    .and_then(|expr| declaration_value_type_in_expr(expr, span, expr_types))
            }),
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
        ExprKind::Tuple(items) => items
            .iter()
            .find_map(|item| declaration_value_type_in_expr(item, span, expr_types)),
        ExprKind::Array(entries) => entries
            .iter()
            .find_map(|e| declaration_value_type_in_expr(e.expr(), span, expr_types)),
        ExprKind::Record(entries) => entries
            .iter()
            .find_map(|e| declaration_value_type_in_expr(e.expr(), span, expr_types)),
        ExprKind::For { iterable, body, .. } => {
            declaration_value_type_in_expr(iterable, span, expr_types)
                .or_else(|| declaration_value_type_in_expr(body, span, expr_types))
        }
        ExprKind::Index { receiver, key, .. } => {
            declaration_value_type_in_expr(receiver, span, expr_types)
                .or_else(|| declaration_value_type_in_expr(key, span, expr_types))
        }
        ExprKind::AssociatedAccess { .. } => None,
        ExprKind::Break(None)
        | ExprKind::Return(None)
        | ExprKind::Continue
        | ExprKind::Number(_)
        | ExprKind::StringLit(_)
        | ExprKind::Bool(_)
        | ExprKind::SyntaxQuote(_)
        | ExprKind::MacroCall { .. }
        | ExprKind::Ident(_)
        | ExprKind::Import(_)
        | ExprKind::Unit => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::analysis::tests::{TestProject, hover_text};
    use lsp_types::Range;

    #[test]
    fn hover_for_associated_function_member_shows_fresh_return() {
        let project = TestProject::new("hover-associated");
        let source = "let mut g = Map::new();\ng\n";
        let (state, uri) = project.open("main.hern", source);

        let text = hover_text(hover(&state, uri, Position::new(0, 18)).expect("hover"));

        assert!(text.starts_with("fn() -> mut Map("), "{text}");
    }

    #[test]
    fn hover_on_fn_keyword_shows_function_type_and_selects_function() {
        let project = TestProject::new("hover-fn-keyword");
        let source = "fn add(x: int) -> int { x }\n";
        let (state, uri) = project.open("main.hern", source);

        let hover = hover(&state, uri, Position::new(0, 0)).expect("hover");
        let text = hover_text(hover.clone());

        assert_eq!(text, "fn(int) -> int");
        assert_eq!(
            hover.range,
            Some(Range::new(Position::new(0, 0), Position::new(0, 27)))
        );
    }

    #[test]
    fn hover_on_lambda_fn_keyword_shows_lambda_type_and_selects_lambda() {
        let project = TestProject::new("hover-lambda-fn-keyword");
        let source = "let f = fn(x: int) { x };\n";
        let (state, uri) = project.open("main.hern", source);

        let hover = hover(&state, uri, Position::new(0, 8)).expect("hover");
        let text = hover_text(hover.clone());

        assert_eq!(text, "fn(int) -> int");
        assert_eq!(
            hover.range,
            Some(Range::new(Position::new(0, 8), Position::new(0, 24)))
        );
    }
}
