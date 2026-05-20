use crate::analysis::CompilerDiagnostic;
use crate::ast::{
    ArrayEntry, Attribute, BinOp, DeriveTrait, Expr, ExprKind, MacroExpansionInfo, Param, Pattern,
    Program, RecordEntry, SourceSpan, Stmt, Type, TypeDef, TypeParam, TypeReturn, Variant,
};
use crate::lex::{Lexer, Spanned, Token};
use crate::parse::Parser;
use crate::syntax::{
    ScopeSet, Syntax, SyntaxDelimiter, SyntaxKind, SyntaxOrigin, SyntaxTemplate, token_to_syntax,
};
use std::collections::HashMap;

use super::registry::{MacroRegistry, collect_macros, collect_macros_with_imports};
use super::runtime::{MacroRuntime, MacroRuntimeLimits};
use super::source::{MappedSyntaxSource, syntax_source_with_map};

const DEFAULT_MAX_EXPANSIONS: usize = 256;
const DEFAULT_MAX_EVAL_STEPS: usize = 20_000;
const DEFAULT_MAX_OUTPUT_SYNTAX_NODES: usize = 10_000;
// Keep the default below the host stack's practical recursion limit. Macro
// helpers are interpreted recursively, so this is a security boundary as well
// as a user-facing diagnostic threshold.
const DEFAULT_MAX_CALL_DEPTH: usize = 16;
const DEFAULT_MAX_GENERATED_SOURCE_BYTES: usize = 1_000_000;
const MACRO_CACHE_ABI_VERSION: &str = concat!("hern-macro-abi:", env!("CARGO_PKG_VERSION"));

pub fn expand_macros(program: &mut Program) -> Result<(), CompilerDiagnostic> {
    expand_macros_with_options(program, MacroExecutionOptions::default())
}

pub fn expand_macros_with_imports<'a>(
    program: &mut Program,
    imports: impl IntoIterator<Item = (&'a str, &'a Program)>,
) -> Result<(), CompilerDiagnostic> {
    expand_macros_with_imports_and_options(program, imports, MacroExecutionOptions::default())
}

#[cfg(test)]
pub(super) fn expand_macros_with_fuel(
    program: &mut Program,
    fuel: usize,
) -> Result<(), CompilerDiagnostic> {
    expand_macros_with_options(
        program,
        MacroExecutionOptions {
            max_expansions: fuel,
            ..MacroExecutionOptions::default()
        },
    )
}

pub fn expand_macros_with_options(
    program: &mut Program,
    options: MacroExecutionOptions,
) -> Result<(), CompilerDiagnostic> {
    let registry = collect_macros(program)?;
    expand_macros_with_registry(program, registry, options)
}

pub fn expand_macros_with_imports_and_options<'a>(
    program: &mut Program,
    imports: impl IntoIterator<Item = (&'a str, &'a Program)>,
    options: MacroExecutionOptions,
) -> Result<(), CompilerDiagnostic> {
    let registry = collect_macros_with_imports(program, imports)?;
    expand_macros_with_registry(program, registry, options)
}

fn expand_macros_with_registry(
    program: &mut Program,
    registry: MacroRegistry,
    options: MacroExecutionOptions,
) -> Result<(), CompilerDiagnostic> {
    let mut ctx = ExpansionCtx {
        registry,
        options,
        macro_expansions: Vec::new(),
        expansion_cache: HashMap::new(),
    };
    expand_top_level_stmts(&mut program.stmts, &mut ctx)?;
    program.macro_expansions.extend(ctx.macro_expansions);
    Ok(())
}

#[cfg(test)]
pub(super) fn expand_macros_with_limits(
    program: &mut Program,
    options: MacroExecutionOptions,
) -> Result<(), CompilerDiagnostic> {
    expand_macros_with_options(program, options)
}

#[derive(Debug, Clone, Copy)]
pub struct MacroExecutionOptions {
    pub max_expansions: usize,
    pub max_eval_steps: usize,
    pub max_output_syntax_nodes: usize,
    pub max_call_depth: usize,
    pub max_generated_source_bytes: usize,
}

impl Default for MacroExecutionOptions {
    fn default() -> Self {
        Self {
            max_expansions: DEFAULT_MAX_EXPANSIONS,
            max_eval_steps: DEFAULT_MAX_EVAL_STEPS,
            max_output_syntax_nodes: DEFAULT_MAX_OUTPUT_SYNTAX_NODES,
            max_call_depth: DEFAULT_MAX_CALL_DEPTH,
            max_generated_source_bytes: DEFAULT_MAX_GENERATED_SOURCE_BYTES,
        }
    }
}

impl MacroExecutionOptions {
    fn runtime_limits(self) -> MacroRuntimeLimits {
        MacroRuntimeLimits {
            eval_steps: self.max_eval_steps,
            output_syntax_nodes: self.max_output_syntax_nodes,
            call_depth: self.max_call_depth,
        }
    }
}

struct ExpansionCtx {
    registry: MacroRegistry,
    options: MacroExecutionOptions,
    macro_expansions: Vec<MacroExpansionInfo>,
    expansion_cache: HashMap<MacroExpansionCacheKey, Syntax>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(super) struct MacroExpansionCacheKey {
    pub(super) macro_definition_hash: u64,
    pub(super) macro_input_hash: u64,
    pub(super) macro_prelude_hash: u64,
    pub(super) compiler_abi_hash: u64,
}

fn expand_top_level_stmts(
    stmts: &mut Vec<Stmt>,
    ctx: &mut ExpansionCtx,
) -> Result<(), CompilerDiagnostic> {
    let mut index = 0;
    while index < stmts.len() {
        if matches!(stmts[index], Stmt::Macro(_)) {
            index += 1;
            continue;
        }
        if let Some(expanded) = expand_derive_macro_stmt(&stmts[index], ctx)? {
            stmts.splice(index..=index, expanded);
            continue;
        }
        if let Some(expanded) = expand_attribute_macro_stmt(&stmts[index], ctx)? {
            stmts.splice(index..=index, expanded);
            continue;
        }
        if let Some(expanded) = expand_item_macro_stmt(&stmts[index], ctx)? {
            stmts.splice(index..=index, expanded);
            continue;
        }
        expand_stmt(&mut stmts[index], ctx)?;
        index += 1;
    }
    Ok(())
}

fn expand_derive_macro_stmt(
    stmt: &Stmt,
    ctx: &mut ExpansionCtx,
) -> Result<Option<Vec<Stmt>>, CompilerDiagnostic> {
    let Stmt::Type(type_def) = stmt else {
        return Ok(None);
    };
    let Some((derive_name, derive_span)) = next_custom_derive(type_def, &ctx.registry)? else {
        return Ok(None);
    };
    let macro_name = derive_macro_name(&derive_name);
    let mut target = type_def.clone();
    remove_one_custom_derive(&mut target, &derive_name);
    let target_source = type_def_to_source(&target);
    let input = source_to_brace_syntax(&target_source, type_def.span)?;
    let (expanded, entry) = run_macro_call(ctx, &macro_name, derive_span, input, type_def.span)?;
    let expansion_site = ExpansionSite {
        macro_name: &macro_name,
        call_span: type_def.span,
        definition_span: entry.def.span,
        generated_source_bytes: ctx.options.max_generated_source_bytes,
    };
    let source_map = expanded_source_map(&expanded);
    let mut program = parse_expanded_items(&expanded, expansion_site)?;
    for stmt in &mut program.stmts {
        rewrite_stmt_spans(stmt, type_def.span, &source_map);
    }
    ctx.macro_expansions.push(MacroExpansionInfo {
        macro_name: macro_name.clone(),
        call_span: type_def.span,
        name_span: derive_span,
        definition_span: entry.def.span,
        generated_source_excerpt: generated_source_excerpt(&source_map.source),
    });

    let mut out = Vec::with_capacity(1 + program.stmts.len());
    out.push(Stmt::Type(target));
    out.extend(program.stmts);
    expand_top_level_stmts(&mut out, ctx)?;
    Ok(Some(out))
}

fn next_custom_derive(
    type_def: &TypeDef,
    registry: &MacroRegistry,
) -> Result<Option<(String, SourceSpan)>, CompilerDiagnostic> {
    for derive in type_def.derives.iter().rev() {
        for trait_name in derive.traits.iter().rev() {
            let DeriveTrait::Custom(name) = trait_name else {
                continue;
            };
            let macro_name = derive_macro_name(name);
            if registry.get(&macro_name).is_none() {
                return Err(CompilerDiagnostic::error(
                    Some(derive.span),
                    format!(
                        "unknown derive macro `{name}`; define macro `{macro_name}` to support #[derive({name})]"
                    ),
                ));
            }
            return Ok(Some((name.clone(), derive.span)));
        }
    }
    Ok(None)
}

fn derive_macro_name(name: &str) -> String {
    format!("derive_{name}")
}

fn remove_one_custom_derive(type_def: &mut TypeDef, name: &str) {
    for derive in &mut type_def.derives {
        if let Some(index) = derive.traits.iter().position(
            |trait_name| matches!(trait_name, DeriveTrait::Custom(candidate) if candidate == name),
        ) {
            derive.traits.remove(index);
            break;
        }
    }
    type_def.derives.retain(|derive| !derive.traits.is_empty());
}

fn expand_attribute_macro_stmt(
    stmt: &Stmt,
    ctx: &mut ExpansionCtx,
) -> Result<Option<Vec<Stmt>>, CompilerDiagnostic> {
    let Stmt::Fn { attrs, span, .. } = stmt else {
        return Ok(None);
    };
    let Some((attr_index, attr)) = attrs
        .iter()
        .enumerate()
        .find(|(_, attr)| !attr.is("test") && ctx.registry.get(&attr.name).is_some())
    else {
        if let Some(attr) = attrs.iter().find(|attr| !attr.is("test")) {
            return Err(CompilerDiagnostic::error(
                Some(attr.span),
                format!("unknown attribute macro `{}`", attr.name),
            ));
        }
        return Ok(None);
    };
    if !attr.args.is_empty() {
        return Err(CompilerDiagnostic::error(
            Some(attr.span),
            format!(
                "attribute macro `{}` does not accept attribute arguments",
                attr.name
            ),
        ));
    }

    let target_source = function_attribute_target_source(stmt, attr_index)?;
    let input = source_to_brace_syntax(&target_source, *span)?;
    let (expanded, entry) = run_macro_call(ctx, &attr.name, attr.span, input, *span)?;
    let expansion_site = ExpansionSite {
        macro_name: &attr.name,
        call_span: *span,
        definition_span: entry.def.span,
        generated_source_bytes: ctx.options.max_generated_source_bytes,
    };
    let source_map = expanded_source_map(&expanded);
    let mut program = parse_expanded_items(&expanded, expansion_site)?;
    for stmt in &mut program.stmts {
        rewrite_stmt_spans(stmt, *span, &source_map);
    }
    ctx.macro_expansions.push(MacroExpansionInfo {
        macro_name: attr.name.clone(),
        call_span: *span,
        name_span: attr.span,
        definition_span: entry.def.span,
        generated_source_excerpt: generated_source_excerpt(&source_map.source),
    });
    expand_top_level_stmts(&mut program.stmts, ctx)?;
    Ok(Some(program.stmts))
}

fn function_attribute_target_source(
    stmt: &Stmt,
    consumed_attr_index: usize,
) -> Result<String, CompilerDiagnostic> {
    let Stmt::Fn {
        attrs,
        name,
        params,
        ret_type,
        body,
        ..
    } = stmt
    else {
        unreachable!("attribute macro target source is only requested for functions");
    };
    let mut out = String::new();
    for (index, attr) in attrs.iter().enumerate() {
        if index != consumed_attr_index {
            out.push_str(&attribute_to_source(attr));
            out.push('\n');
        }
    }
    out.push_str("fn ");
    out.push_str(name);
    out.push('(');
    out.push_str(
        &params
            .iter()
            .map(param_to_source)
            .collect::<Vec<_>>()
            .join(", "),
    );
    out.push(')');
    if let Some(ret_type) = ret_type {
        out.push_str(" -> ");
        out.push_str(&type_return_to_source(ret_type));
    }
    out.push(' ');
    out.push_str(&expr_to_source(body)?);
    Ok(out)
}

fn attribute_to_source(attr: &Attribute) -> String {
    if attr.args.is_empty() {
        format!("#[{}]", attr.name)
    } else {
        format!("#[{}({})]", attr.name, attr.args.join(", "))
    }
}

fn type_def_to_source(type_def: &TypeDef) -> String {
    let mut out = String::new();
    for derive in &type_def.derives {
        let args = derive
            .traits
            .iter()
            .map(|trait_name| trait_name.name().to_string())
            .collect::<Vec<_>>()
            .join(", ");
        out.push_str(&format!("#[derive({args})]\n"));
    }
    out.push_str("type ");
    out.push_str(&type_def.name);
    if !type_def.params.is_empty() {
        out.push('(');
        out.push_str(&type_def.params.join(", "));
        out.push(')');
    }
    out.push_str(" = ");
    if type_def.variants.is_empty() {
        out.push('*');
    } else {
        out.push_str(
            &type_def
                .variants
                .iter()
                .map(variant_to_source)
                .collect::<Vec<_>>()
                .join(" | "),
        );
    }
    out
}

fn variant_to_source(variant: &Variant) -> String {
    let mut out = String::new();
    for attr in &variant.attrs {
        out.push_str(&attribute_to_source(attr));
        out.push(' ');
    }
    out.push_str(&variant.name);
    if let Some(payload) = &variant.payload {
        out.push('(');
        out.push_str(&type_to_source(payload));
        out.push(')');
    }
    out
}

fn param_to_source(param: &Param) -> String {
    let mut out = String::new();
    if param.mut_place {
        out.push_str("mut ");
    }
    out.push_str(&pattern_to_source(&param.pat));
    if let Some(ty) = &param.ty {
        out.push_str(": ");
        out.push_str(&type_to_source(ty));
    }
    out
}

fn type_param_to_source(param: &TypeParam) -> String {
    if param.mut_place {
        format!("mut {}", type_to_source(&param.ty))
    } else {
        type_to_source(&param.ty)
    }
}

fn type_return_to_source(ret: &TypeReturn) -> String {
    if ret.mut_place {
        format!("mut {}", type_to_source(&ret.ty))
    } else {
        type_to_source(&ret.ty)
    }
}

fn type_to_source(ty: &Type) -> String {
    match ty {
        Type::Ident(name) | Type::Var(name) => name.clone(),
        Type::App(con, args) => format!(
            "{}({})",
            type_to_source(con),
            args.iter()
                .map(type_to_source)
                .collect::<Vec<_>>()
                .join(", ")
        ),
        Type::Func(params, ret) => format!(
            "fn({}) -> {}",
            params
                .iter()
                .map(type_param_to_source)
                .collect::<Vec<_>>()
                .join(", "),
            type_return_to_source(ret)
        ),
        Type::Tuple(items) => format!(
            "({})",
            items
                .iter()
                .map(type_to_source)
                .collect::<Vec<_>>()
                .join(", ")
        ),
        Type::Record(fields, is_open) => {
            let mut parts = fields
                .iter()
                .map(|(name, ty)| format!("{name}: {}", type_to_source(ty)))
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

fn pattern_to_source(pattern: &Pattern) -> String {
    match pattern {
        Pattern::Wildcard => "_".to_string(),
        Pattern::StringLit(value) => format!("{value:?}"),
        Pattern::NumberLit(value) => value.as_lua_source(),
        Pattern::BoolLit(value) => value.to_string(),
        Pattern::IntRange {
            start,
            end,
            inclusive,
        } => format!("{start}{}{end}", if *inclusive { "..=" } else { ".." }),
        Pattern::Variable(name, _) => name.clone(),
        Pattern::Constructor { name, binding } => binding
            .as_ref()
            .map(|binding| format!("{name}({})", pattern_to_source(binding)))
            .unwrap_or_else(|| name.clone()),
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
            let mut parts = elements.iter().map(pattern_to_source).collect::<Vec<_>>();
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
                .map(pattern_to_source)
                .collect::<Vec<_>>()
                .join(", ")
        ),
        Pattern::SyntaxQuote(_) => "'(...)".to_string(),
    }
}

fn expr_to_source(expr: &Expr) -> Result<String, CompilerDiagnostic> {
    Ok(match &expr.kind {
        ExprKind::Number(value) => value.as_lua_source(),
        ExprKind::StringLit(value) => format!("{value:?}"),
        ExprKind::Bool(value) => value.to_string(),
        ExprKind::Ident(name) => name.clone(),
        ExprKind::Grouped(inner) => format!("({})", expr_to_source(inner)?),
        ExprKind::Not(inner) => format!("!{}", expr_to_source(inner)?),
        ExprKind::Neg { operand, .. } => format!("-{}", expr_to_source(operand)?),
        ExprKind::Assign { target, value } => {
            format!("{} = {}", expr_to_source(target)?, expr_to_source(value)?)
        }
        ExprKind::Binary { lhs, op, rhs, .. } => format!(
            "{} {} {}",
            expr_to_source(lhs)?,
            bin_op_to_source(op),
            expr_to_source(rhs)?
        ),
        ExprKind::Range {
            start,
            end,
            inclusive,
        } => format!(
            "{}{}{}",
            start
                .as_deref()
                .map(expr_to_source)
                .transpose()?
                .unwrap_or_default(),
            if *inclusive { "..=" } else { ".." },
            end.as_deref()
                .map(expr_to_source)
                .transpose()?
                .unwrap_or_default()
        ),
        ExprKind::Call { callee, args, .. } => format!(
            "{}({})",
            expr_to_source(callee)?,
            args.iter()
                .map(expr_to_source)
                .collect::<Result<Vec<_>, _>>()?
                .join(", ")
        ),
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
        } => format!(
            "if {} {} else {}",
            expr_to_source(cond)?,
            expr_to_source(then_branch)?,
            expr_to_source(else_branch)?
        ),
        ExprKind::Match { scrutinee, arms } => format!(
            "match {} {{ {} }}",
            expr_to_source(scrutinee)?,
            arms.iter()
                .map(|(pattern, body)| Ok(format!(
                    "{} -> {}",
                    pattern_to_source(pattern),
                    expr_to_source(body)?
                )))
                .collect::<Result<Vec<_>, CompilerDiagnostic>>()?
                .join(", ")
        ),
        ExprKind::Loop(body) => format!("loop {}", expr_to_source(body)?),
        ExprKind::Break(Some(value)) => format!("break {}", expr_to_source(value)?),
        ExprKind::Break(None) => "break".to_string(),
        ExprKind::Continue => "continue".to_string(),
        ExprKind::Return(Some(value)) => format!("return {}", expr_to_source(value)?),
        ExprKind::Return(None) => "return".to_string(),
        ExprKind::Block { stmts, final_expr } => {
            let mut parts = stmts
                .iter()
                .map(stmt_to_source)
                .collect::<Result<Vec<_>, _>>()?;
            if let Some(final_expr) = final_expr {
                parts.push(expr_to_source(final_expr)?);
            }
            format!("{{ {} }}", parts.join(" "))
        }
        ExprKind::Tuple(items) => format!(
            "({})",
            items
                .iter()
                .map(expr_to_source)
                .collect::<Result<Vec<_>, _>>()?
                .join(", ")
        ),
        ExprKind::Array(entries) => format!(
            "[{}]",
            entries
                .iter()
                .map(|entry| match entry {
                    ArrayEntry::Elem(expr) => expr_to_source(expr),
                    ArrayEntry::Spread(expr) => Ok(format!("..{}", expr_to_source(expr)?)),
                })
                .collect::<Result<Vec<_>, CompilerDiagnostic>>()?
                .join(", ")
        ),
        ExprKind::Record(entries) => format!(
            "#{{ {} }}",
            entries
                .iter()
                .map(|entry| match entry {
                    RecordEntry::Field(name, expr) =>
                        Ok(format!("{name}: {}", expr_to_source(expr)?)),
                    RecordEntry::Spread(expr) => Ok(format!("..{}", expr_to_source(expr)?)),
                })
                .collect::<Result<Vec<_>, CompilerDiagnostic>>()?
                .join(", ")
        ),
        ExprKind::FieldAccess { expr, field, .. } => {
            format!("{}.{}", expr_to_source(expr)?, field)
        }
        ExprKind::Index { receiver, key, .. } => {
            format!("{}[{}]", expr_to_source(receiver)?, expr_to_source(key)?)
        }
        ExprKind::AssociatedAccess { target, member, .. } => {
            format!("{}::{member}", type_to_source(target))
        }
        ExprKind::MacroCall { name, input, .. } => {
            format!("{name}!{}", crate::syntax::syntax_to_source(input))
        }
        ExprKind::Import(path) => format!("import {path:?}"),
        ExprKind::Lambda {
            params,
            return_type,
            body,
            ..
        } => {
            let mut out = format!(
                "fn({})",
                params
                    .iter()
                    .map(param_to_source)
                    .collect::<Vec<_>>()
                    .join(", ")
            );
            if let Some(return_type) = return_type {
                out.push_str(" -> ");
                out.push_str(&type_to_source(return_type));
            }
            out.push(' ');
            out.push_str(&expr_to_source(body)?);
            out
        }
        ExprKind::SyntaxQuote(template) => {
            format!("'{}", syntax_template_to_source(template))
        }
        ExprKind::For {
            pat,
            iterable,
            body,
            ..
        } => format!(
            "for {} in {} {}",
            pattern_to_source(pat),
            expr_to_source(iterable)?,
            expr_to_source(body)?
        ),
        ExprKind::Unit => "()".to_string(),
    })
}

fn stmt_to_source(stmt: &Stmt) -> Result<String, CompilerDiagnostic> {
    Ok(match stmt {
        Stmt::Let {
            pat,
            is_mutable,
            ty,
            value,
            ..
        } => {
            let mut out = "let ".to_string();
            if *is_mutable {
                out.push_str("mut ");
            }
            out.push_str(&pattern_to_source(pat));
            if let Some(ty) = ty {
                out.push_str(": ");
                out.push_str(&type_to_source(ty));
            }
            out.push_str(" = ");
            out.push_str(&expr_to_source(value)?);
            out.push(';');
            out
        }
        Stmt::Expr(expr) => format!("{};", expr_to_source(expr)?),
        Stmt::Fn { .. } => function_attribute_target_source(stmt, usize::MAX)?,
        _ => {
            return Err(CompilerDiagnostic::error(
                Some(stmt.span()),
                "attribute macro target contains a statement that cannot be reified yet",
            ));
        }
    })
}

fn bin_op_to_source(op: &BinOp) -> &str {
    match op {
        BinOp::Pipe => "|>",
        BinOp::Custom(op) => op,
    }
}

fn source_to_brace_syntax(
    source: &str,
    fallback_span: SourceSpan,
) -> Result<Syntax, CompilerDiagnostic> {
    let wrapped = format!("{{ {source} }}");
    let tokens = Lexer::new(&wrapped).tokenize().map_err(|err| {
        CompilerDiagnostic::error(
            Some(fallback_span),
            format!(
                "attribute macro target could not be tokenized: {:?}",
                err.kind
            ),
        )
    })?;
    let (syntax, next) = parse_syntax_tree_tokens(&tokens, 0, fallback_span)?;
    if !matches!(tokens.get(next).map(|token| &token.token), Some(Token::Eof)) {
        return Err(CompilerDiagnostic::error(
            Some(fallback_span),
            "attribute macro target produced trailing syntax after token-tree reconstruction",
        ));
    }
    Ok(syntax)
}

fn parse_syntax_tree_tokens(
    tokens: &[Spanned],
    start: usize,
    fallback_span: SourceSpan,
) -> Result<(Syntax, usize), CompilerDiagnostic> {
    let Some(open) = tokens.get(start) else {
        return Err(CompilerDiagnostic::error(
            Some(fallback_span),
            "attribute macro target ended before syntax tree could be reconstructed",
        ));
    };
    let (delimiter, close_token) = match open.token {
        Token::LParen => (SyntaxDelimiter::Paren, Token::RParen),
        Token::LBrace => (SyntaxDelimiter::Brace, Token::RBrace),
        Token::LBracket => (SyntaxDelimiter::Bracket, Token::RBracket),
        _ => {
            return Err(CompilerDiagnostic::error(
                Some(fallback_span),
                "attribute macro target reconstruction expected a delimiter",
            ));
        }
    };

    let mut children = Vec::new();
    let mut index = start + 1;
    loop {
        let Some(token) = tokens.get(index) else {
            return Err(CompilerDiagnostic::error(
                Some(fallback_span),
                "attribute macro target has an unterminated syntax tree",
            ));
        };
        if token.token == close_token {
            let span = SourceSpan::from_bounds(open.span, token.span);
            return Ok((
                Syntax {
                    kind: SyntaxKind::Tree {
                        delimiter,
                        children,
                    },
                    span,
                    origin: SyntaxOrigin::Generated,
                    scopes: ScopeSet::generated(),
                },
                index + 1,
            ));
        }
        match token.token {
            Token::LParen | Token::LBrace | Token::LBracket => {
                let (child, next) = parse_syntax_tree_tokens(tokens, index, fallback_span)?;
                children.push(child);
                index = next;
            }
            Token::RParen | Token::RBrace | Token::RBracket | Token::Eof => {
                return Err(CompilerDiagnostic::error(
                    Some(fallback_span),
                    format!(
                        "attribute macro target has mismatched delimiter near {}",
                        token.token
                    ),
                ));
            }
            _ => {
                let Some(syntax) = token_to_syntax(token) else {
                    return Err(CompilerDiagnostic::error(
                        Some(fallback_span),
                        format!(
                            "attribute macro target contains unsupported token {}",
                            token.token
                        ),
                    ));
                };
                children.push(Syntax {
                    origin: SyntaxOrigin::Generated,
                    scopes: ScopeSet::generated(),
                    ..syntax
                });
                index += 1;
            }
        }
    }
}

fn syntax_template_to_source(template: &SyntaxTemplate) -> String {
    match template {
        SyntaxTemplate::Token { token, .. } => crate::syntax::syntax_token_to_source(token),
        SyntaxTemplate::Tree {
            delimiter,
            children,
            ..
        } => {
            let (open, close) = match delimiter {
                SyntaxDelimiter::Paren => ("(", ")"),
                SyntaxDelimiter::Brace => ("{", "}"),
                SyntaxDelimiter::Bracket => ("[", "]"),
            };
            format!(
                "{open}{}{close}",
                children
                    .iter()
                    .map(syntax_template_to_source)
                    .collect::<Vec<_>>()
                    .join(" ")
            )
        }
        SyntaxTemplate::Splice { name, repeat, .. } => {
            if *repeat {
                format!("${name}..")
            } else {
                format!("${name}")
            }
        }
    }
}

fn expand_stmts(stmts: &mut [Stmt], ctx: &mut ExpansionCtx) -> Result<(), CompilerDiagnostic> {
    for stmt in stmts {
        expand_stmt(stmt, ctx)?;
    }
    Ok(())
}

fn expand_stmt(stmt: &mut Stmt, ctx: &mut ExpansionCtx) -> Result<(), CompilerDiagnostic> {
    match stmt {
        Stmt::Let { value, .. } | Stmt::Expr(value) => expand_expr(value, ctx),
        Stmt::Fn { body, .. } | Stmt::Op { body, .. } => expand_expr(body, ctx),
        Stmt::Impl(id) => {
            for method in &mut id.methods {
                expand_expr(&mut method.body, ctx)?;
            }
            Ok(())
        }
        Stmt::InherentImpl(id) => {
            for method in &mut id.methods {
                expand_expr(&mut method.body, ctx)?;
            }
            Ok(())
        }
        Stmt::TestBlock { stmts, .. } | Stmt::RecBlock { stmts, .. } => expand_stmts(stmts, ctx),
        Stmt::Macro(_) => Err(CompilerDiagnostic::error(
            Some(stmt.span()),
            "macro definitions are only allowed at the top level",
        )),
        Stmt::Trait(_) | Stmt::Type(_) | Stmt::TypeAlias { .. } | Stmt::Extern { .. } => Ok(()),
    }
}

fn expand_item_macro_stmt(
    stmt: &Stmt,
    ctx: &mut ExpansionCtx,
) -> Result<Option<Vec<Stmt>>, CompilerDiagnostic> {
    let Stmt::Expr(expr) = stmt else {
        return Ok(None);
    };
    let ExprKind::MacroCall {
        name,
        name_span,
        input,
        ..
    } = &expr.kind
    else {
        return Ok(None);
    };
    let (expanded, entry) = run_macro_call(ctx, name, *name_span, input.clone(), expr.span)?;
    let expansion_site = ExpansionSite {
        macro_name: name,
        call_span: expr.span,
        definition_span: entry.def.span,
        generated_source_bytes: ctx.options.max_generated_source_bytes,
    };
    let source_map = expanded_source_map(&expanded);
    match parse_expanded_expr(&expanded, expansion_site) {
        Ok(mut expanded_expr) => {
            rewrite_expr_spans(&mut expanded_expr, expr.span, &source_map);
            ctx.macro_expansions.push(MacroExpansionInfo {
                macro_name: name.clone(),
                call_span: expr.span,
                name_span: *name_span,
                definition_span: entry.def.span,
                generated_source_excerpt: generated_source_excerpt(&source_map.source),
            });
            expand_expr(&mut expanded_expr, ctx)?;
            return Ok(Some(vec![Stmt::Expr(expanded_expr)]));
        }
        Err(expr_error) => {
            let Ok(program) = parse_expanded_items(&expanded, expansion_site) else {
                return Err(expr_error);
            };
            if !program
                .stmts
                .iter()
                .any(|stmt| !matches!(stmt, Stmt::Expr(_)))
            {
                return Err(expr_error);
            }
            return finish_item_macro_expansion(
                program,
                expr,
                name,
                *name_span,
                &entry,
                &source_map,
                ctx,
            );
        }
    }
}

fn finish_item_macro_expansion(
    mut program: Program,
    call_expr: &Expr,
    name: &str,
    name_span: SourceSpan,
    entry: &super::registry::MacroEntry,
    source_map: &MappedSyntaxSource,
    ctx: &mut ExpansionCtx,
) -> Result<Option<Vec<Stmt>>, CompilerDiagnostic> {
    for stmt in &mut program.stmts {
        rewrite_stmt_spans(stmt, call_expr.span, &source_map);
    }
    ctx.macro_expansions.push(MacroExpansionInfo {
        macro_name: name.to_string(),
        call_span: call_expr.span,
        name_span,
        definition_span: entry.def.span,
        generated_source_excerpt: generated_source_excerpt(&source_map.source),
    });
    expand_top_level_stmts(&mut program.stmts, ctx)?;
    Ok(Some(program.stmts))
}

fn expand_expr(expr: &mut Expr, ctx: &mut ExpansionCtx) -> Result<(), CompilerDiagnostic> {
    match &mut expr.kind {
        ExprKind::MacroCall {
            name,
            name_span,
            input,
            ..
        } => {
            let (expanded, entry) =
                run_macro_call(ctx, name, *name_span, input.clone(), expr.span)?;
            let expansion_site = ExpansionSite {
                macro_name: name,
                call_span: expr.span,
                definition_span: entry.def.span,
                generated_source_bytes: ctx.options.max_generated_source_bytes,
            };
            let source_map = expanded_source_map(&expanded);
            let mut expanded_expr = parse_expanded_expr(&expanded, expansion_site)?;
            rewrite_expr_spans(&mut expanded_expr, expr.span, &source_map);
            ctx.macro_expansions.push(MacroExpansionInfo {
                macro_name: name.clone(),
                call_span: expr.span,
                name_span: *name_span,
                definition_span: entry.def.span,
                generated_source_excerpt: generated_source_excerpt(&source_map.source),
            });
            *expr = expanded_expr;
            expand_expr(expr, ctx)
        }
        ExprKind::Grouped(inner)
        | ExprKind::Not(inner)
        | ExprKind::Loop(inner)
        | ExprKind::Break(Some(inner))
        | ExprKind::Return(Some(inner))
        | ExprKind::FieldAccess { expr: inner, .. }
        | ExprKind::Lambda { body: inner, .. } => expand_expr(inner, ctx),
        ExprKind::Neg { operand, .. } => expand_expr(operand, ctx),
        ExprKind::Assign { target, value } => {
            expand_expr(target, ctx)?;
            expand_expr(value, ctx)
        }
        ExprKind::Binary { lhs, rhs, .. } => {
            expand_expr(lhs, ctx)?;
            expand_expr(rhs, ctx)
        }
        ExprKind::Range { start, end, .. } => {
            if let Some(start) = start {
                expand_expr(start, ctx)?;
            }
            if let Some(end) = end {
                expand_expr(end, ctx)?;
            }
            Ok(())
        }
        ExprKind::Call { callee, args, .. } => {
            expand_expr(callee, ctx)?;
            for arg in args {
                expand_expr(arg, ctx)?;
            }
            Ok(())
        }
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
        } => {
            expand_expr(cond, ctx)?;
            expand_expr(then_branch, ctx)?;
            expand_expr(else_branch, ctx)
        }
        ExprKind::Match { scrutinee, arms } => {
            expand_expr(scrutinee, ctx)?;
            for (_, body) in arms {
                expand_expr(body, ctx)?;
            }
            Ok(())
        }
        ExprKind::Block { stmts, final_expr } => {
            expand_stmts(stmts, ctx)?;
            if let Some(expr) = final_expr {
                expand_expr(expr, ctx)?;
            }
            Ok(())
        }
        ExprKind::Tuple(items) => {
            for item in items {
                expand_expr(item, ctx)?;
            }
            Ok(())
        }
        ExprKind::Array(entries) => {
            for entry in entries {
                expand_expr(entry.expr_mut(), ctx)?;
            }
            Ok(())
        }
        ExprKind::Record(entries) => {
            for entry in entries {
                expand_expr(entry.expr_mut(), ctx)?;
            }
            Ok(())
        }
        ExprKind::Index { receiver, key, .. } => {
            expand_expr(receiver, ctx)?;
            expand_expr(key, ctx)
        }
        ExprKind::For { iterable, body, .. } => {
            expand_expr(iterable, ctx)?;
            expand_expr(body, ctx)
        }
        ExprKind::Number(_)
        | ExprKind::StringLit(_)
        | ExprKind::Bool(_)
        | ExprKind::SyntaxQuote(_)
        | ExprKind::Ident(_)
        | ExprKind::AssociatedAccess { .. }
        | ExprKind::Import(_)
        | ExprKind::Break(None)
        | ExprKind::Continue
        | ExprKind::Return(None)
        | ExprKind::Unit => Ok(()),
    }
}

fn run_macro_call(
    ctx: &mut ExpansionCtx,
    name: &str,
    name_span: SourceSpan,
    input: Syntax,
    call_span: SourceSpan,
) -> Result<(Syntax, super::registry::MacroEntry), CompilerDiagnostic> {
    if ctx.options.max_expansions == 0 {
        return Err(CompilerDiagnostic::error(
            Some(name_span),
            "macro expansion fuel exhausted",
        ));
    }
    ctx.options.max_expansions -= 1;
    let entry = ctx.registry.get(name).cloned().ok_or_else(|| {
        CompilerDiagnostic::error(Some(name_span), format!("unknown macro `{name}!`"))
    })?;
    let cache_key = macro_expansion_cache_key(&entry.def, &input);
    if let Some(expanded) = ctx.expansion_cache.get(&cache_key).cloned() {
        return Ok((expanded, entry));
    }
    let runtime = MacroRuntime::new(ctx.options.runtime_limits(), entry.helpers.clone());
    let expanded = runtime
        .run_macro(&entry.def, input, call_span)
        .map_err(|err| {
            let mut diagnostic = CompilerDiagnostic::error(
                Some(err.span),
                format!("macro `{name}!`: {}", err.message),
            )
            .with_related(call_span, format!("while expanding `{name}!` here"))
            .with_related(
                entry.def.span,
                format!("macro `{}` is defined here", entry.def.name),
            );
            for related in err.related {
                diagnostic = diagnostic.with_related(related.span, related.message);
            }
            diagnostic
        })?;
    ctx.expansion_cache.insert(cache_key, expanded.clone());
    Ok((expanded, entry))
}

pub(super) fn macro_expansion_cache_key(
    def: &crate::ast::MacroDef,
    input: &Syntax,
) -> MacroExpansionCacheKey {
    MacroExpansionCacheKey {
        macro_definition_hash: stable_hash(&format!("{def:?}")),
        macro_input_hash: stable_hash(&format!("{input:?}")),
        macro_prelude_hash: stable_hash("compiler-owned-macro-prelude-v1"),
        compiler_abi_hash: stable_hash(MACRO_CACHE_ABI_VERSION),
    }
}

fn stable_hash(text: &str) -> u64 {
    let mut hash = 0xcbf2_9ce4_8422_2325u64;
    for byte in text.as_bytes() {
        hash ^= u64::from(*byte);
        hash = hash.wrapping_mul(0x0000_0100_0000_01b3);
    }
    hash
}

#[derive(Debug, Clone, Copy)]
struct ExpansionSite<'a> {
    macro_name: &'a str,
    call_span: SourceSpan,
    definition_span: SourceSpan,
    generated_source_bytes: usize,
}

fn parse_expanded_expr(
    syntax: &Syntax,
    site: ExpansionSite<'_>,
) -> Result<Expr, CompilerDiagnostic> {
    let mapped_source = syntax_source_with_map(syntax);
    let source = &mapped_source.source;
    if source.len() > site.generated_source_bytes {
        return Err(CompilerDiagnostic::error(
            Some(site.call_span),
            format!(
                "macro `{}` generated too much source: {} bytes exceeds limit {}",
                site.macro_name,
                source.len(),
                site.generated_source_bytes
            ),
        ));
    }
    let tokens = Lexer::new(&source).tokenize().map_err(|err| {
        let err_span = SourceSpan::from_lex_span(err.span);
        CompilerDiagnostic::error(
            Some(site.call_span),
            format!(
                "macro `{}` expansion produced invalid tokens: {:?}\nmacro definition starts at {}:{}{}\ngenerated source:\n{}",
                site.macro_name,
                err.kind,
                site.definition_span.start_line,
                site.definition_span.start_col,
                syntax_origin_note(mapped_source.origin_at(err_span)),
                generated_source_excerpt(&source)
            ),
        )
        .with_related(
            site.call_span,
            format!("while expanding `{}!` here", site.macro_name),
        )
        .with_related(
            site.definition_span,
            format!("macro `{}` is defined here", site.macro_name),
        )
    })?;
    Parser::new(&tokens).parse_expr_fragment().map_err(|err| {
        let err_span = SourceSpan::from_lex_span(err.span);
        CompilerDiagnostic::error(
            Some(site.call_span),
            format!(
                "macro `{}` expansion did not produce an expression: {}\nmacro definition starts at {}:{}{}\ngenerated source:\n{}",
                site.macro_name,
                err.message,
                site.definition_span.start_line,
                site.definition_span.start_col,
                syntax_origin_note(mapped_source.origin_at(err_span)),
                generated_source_excerpt(&source)
            ),
        )
        .with_related(
            site.call_span,
            format!("while expanding `{}!` here", site.macro_name),
        )
        .with_related(
            site.definition_span,
            format!("macro `{}` is defined here", site.macro_name),
        )
    })
}

fn parse_expanded_items(
    syntax: &Syntax,
    site: ExpansionSite<'_>,
) -> Result<Program, CompilerDiagnostic> {
    let mapped_source = syntax_source_with_map(syntax);
    let source = &mapped_source.source;
    if source.len() > site.generated_source_bytes {
        return Err(CompilerDiagnostic::error(
            Some(site.call_span),
            format!(
                "macro `{}` generated too much source: {} bytes exceeds limit {}",
                site.macro_name,
                source.len(),
                site.generated_source_bytes
            ),
        ));
    }
    let tokens = Lexer::new(source).tokenize().map_err(|err| {
        let err_span = SourceSpan::from_lex_span(err.span);
        CompilerDiagnostic::error(
            Some(site.call_span),
            format!(
                "macro `{}` item expansion produced invalid tokens: {:?}\nmacro definition starts at {}:{}{}\ngenerated source:\n{}",
                site.macro_name,
                err.kind,
                site.definition_span.start_line,
                site.definition_span.start_col,
                syntax_origin_note(mapped_source.origin_at(err_span)),
                generated_source_excerpt(source)
            ),
        )
        .with_related(
            site.call_span,
            format!("while expanding `{}!` here", site.macro_name),
        )
        .with_related(
            site.definition_span,
            format!("macro `{}` is defined here", site.macro_name),
        )
    })?;
    Parser::new(&tokens).parse_program().map_err(|err| {
        let err_span = SourceSpan::from_lex_span(err.span);
        CompilerDiagnostic::error(
            Some(site.call_span),
            format!(
                "macro `{}` expansion did not produce valid items: {}\nmacro definition starts at {}:{}{}\ngenerated source:\n{}",
                site.macro_name,
                err.message,
                site.definition_span.start_line,
                site.definition_span.start_col,
                syntax_origin_note(mapped_source.origin_at(err_span)),
                generated_source_excerpt(source)
            ),
        )
        .with_related(
            site.call_span,
            format!("while expanding `{}!` here", site.macro_name),
        )
        .with_related(
            site.definition_span,
            format!("macro `{}` is defined here", site.macro_name),
        )
    })
}

fn expanded_source_map(syntax: &Syntax) -> MappedSyntaxSource {
    syntax_source_with_map(syntax)
}

fn syntax_origin_note(origin: Option<String>) -> String {
    origin
        .map(|origin| format!("\nsyntax origin: {origin}"))
        .unwrap_or_default()
}

fn generated_source_excerpt(source: &str) -> String {
    const MAX_EXCERPT_CHARS: usize = 240;
    let mut excerpt = String::new();
    for (index, ch) in source.chars().enumerate() {
        if index == MAX_EXCERPT_CHARS {
            excerpt.push_str("...");
            return excerpt;
        }
        excerpt.push(ch);
    }
    excerpt
}

fn rewrite_expr_spans(expr: &mut Expr, fallback_span: SourceSpan, source_map: &MappedSyntaxSource) {
    expr.span = expanded_ast_span(expr.span, fallback_span, source_map);
    match &mut expr.kind {
        ExprKind::Grouped(inner)
        | ExprKind::Not(inner)
        | ExprKind::Loop(inner)
        | ExprKind::Break(Some(inner))
        | ExprKind::Return(Some(inner))
        | ExprKind::Lambda { body: inner, .. } => {
            rewrite_expr_spans(inner, fallback_span, source_map)
        }
        ExprKind::FieldAccess {
            expr: inner,
            field_span,
            ..
        } => {
            *field_span = expanded_ast_span(*field_span, fallback_span, source_map);
            rewrite_expr_spans(inner, fallback_span, source_map);
        }
        ExprKind::Neg {
            operand, op_span, ..
        } => {
            *op_span = expanded_ast_span(*op_span, fallback_span, source_map);
            rewrite_expr_spans(operand, fallback_span, source_map);
        }
        ExprKind::Assign { target, value } => {
            rewrite_expr_spans(target, fallback_span, source_map);
            rewrite_expr_spans(value, fallback_span, source_map);
        }
        ExprKind::Binary {
            lhs, op_span, rhs, ..
        } => {
            *op_span = expanded_ast_span(*op_span, fallback_span, source_map);
            rewrite_expr_spans(lhs, fallback_span, source_map);
            rewrite_expr_spans(rhs, fallback_span, source_map);
        }
        ExprKind::Range { start, end, .. } => {
            if let Some(start) = start {
                rewrite_expr_spans(start, fallback_span, source_map);
            }
            if let Some(end) = end {
                rewrite_expr_spans(end, fallback_span, source_map);
            }
        }
        ExprKind::Call { callee, args, .. } => {
            rewrite_expr_spans(callee, fallback_span, source_map);
            for arg in args {
                rewrite_expr_spans(arg, fallback_span, source_map);
            }
        }
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
        } => {
            rewrite_expr_spans(cond, fallback_span, source_map);
            rewrite_expr_spans(then_branch, fallback_span, source_map);
            rewrite_expr_spans(else_branch, fallback_span, source_map);
        }
        ExprKind::Match { scrutinee, arms } => {
            rewrite_expr_spans(scrutinee, fallback_span, source_map);
            for (pattern, body) in arms {
                rewrite_pattern_spans(pattern, fallback_span, source_map);
                rewrite_expr_spans(body, fallback_span, source_map);
            }
        }
        ExprKind::Block { stmts, final_expr } => {
            for stmt in stmts {
                rewrite_stmt_spans(stmt, fallback_span, source_map);
            }
            if let Some(final_expr) = final_expr {
                rewrite_expr_spans(final_expr, fallback_span, source_map);
            }
        }
        ExprKind::Tuple(items) => {
            for item in items {
                rewrite_expr_spans(item, fallback_span, source_map);
            }
        }
        ExprKind::Array(entries) => {
            for entry in entries {
                match entry {
                    ArrayEntry::Elem(expr) | ArrayEntry::Spread(expr) => {
                        rewrite_expr_spans(expr, fallback_span, source_map)
                    }
                }
            }
        }
        ExprKind::Record(entries) => {
            for entry in entries {
                rewrite_expr_spans(entry.expr_mut(), fallback_span, source_map);
            }
        }
        ExprKind::Index { receiver, key, .. } => {
            rewrite_expr_spans(receiver, fallback_span, source_map);
            rewrite_expr_spans(key, fallback_span, source_map);
        }
        ExprKind::AssociatedAccess {
            target_span,
            member_span,
            ..
        } => {
            *target_span = expanded_ast_span(*target_span, fallback_span, source_map);
            *member_span = expanded_ast_span(*member_span, fallback_span, source_map);
        }
        ExprKind::For {
            pat,
            iterable,
            body,
            ..
        } => {
            rewrite_pattern_spans(pat, fallback_span, source_map);
            rewrite_expr_spans(iterable, fallback_span, source_map);
            rewrite_expr_spans(body, fallback_span, source_map);
        }
        ExprKind::MacroCall {
            name_span,
            bang_span,
            ..
        } => {
            *name_span = expanded_ast_span(*name_span, fallback_span, source_map);
            *bang_span = expanded_ast_span(*bang_span, fallback_span, source_map);
        }
        ExprKind::Number(_)
        | ExprKind::StringLit(_)
        | ExprKind::Bool(_)
        | ExprKind::Ident(_)
        | ExprKind::Import(_)
        | ExprKind::Break(None)
        | ExprKind::Continue
        | ExprKind::Return(None)
        | ExprKind::SyntaxQuote(_)
        | ExprKind::Unit => {}
    }
}

fn expanded_ast_span(
    generated_span: SourceSpan,
    fallback_span: SourceSpan,
    source_map: &MappedSyntaxSource,
) -> SourceSpan {
    source_map
        .original_source_span_at(generated_span)
        .unwrap_or(fallback_span)
}

fn rewrite_stmt_spans(stmt: &mut Stmt, fallback_span: SourceSpan, source_map: &MappedSyntaxSource) {
    match stmt {
        Stmt::Let {
            span: stmt_span,
            pat,
            ty: _,
            value,
            ..
        } => {
            *stmt_span = expanded_ast_span(*stmt_span, fallback_span, source_map);
            rewrite_pattern_spans(pat, fallback_span, source_map);
            rewrite_expr_spans(value, fallback_span, source_map);
        }
        Stmt::Expr(expr) => rewrite_expr_spans(expr, fallback_span, source_map),
        Stmt::Fn {
            span: stmt_span,
            name_span,
            params,
            body,
            ..
        }
        | Stmt::Op {
            span: stmt_span,
            name_span,
            params,
            body,
            ..
        } => {
            *stmt_span = expanded_ast_span(*stmt_span, fallback_span, source_map);
            *name_span = expanded_ast_span(*name_span, fallback_span, source_map);
            for param in params {
                rewrite_pattern_spans(&mut param.pat, fallback_span, source_map);
            }
            rewrite_expr_spans(body, fallback_span, source_map);
        }
        Stmt::TestBlock {
            span: stmt_span,
            stmts,
        }
        | Stmt::RecBlock {
            span: stmt_span,
            stmts,
        } => {
            *stmt_span = expanded_ast_span(*stmt_span, fallback_span, source_map);
            for stmt in stmts {
                rewrite_stmt_spans(stmt, fallback_span, source_map);
            }
        }
        Stmt::Macro(_)
        | Stmt::Trait(_)
        | Stmt::Type(_)
        | Stmt::TypeAlias { .. }
        | Stmt::Extern { .. }
        | Stmt::Impl(_)
        | Stmt::InherentImpl(_) => {}
    }
}

fn rewrite_pattern_spans(
    pattern: &mut Pattern,
    fallback_span: SourceSpan,
    source_map: &MappedSyntaxSource,
) {
    match pattern {
        Pattern::Variable(_, binding_span) => {
            *binding_span = expanded_ast_span(*binding_span, fallback_span, source_map)
        }
        Pattern::Constructor {
            binding: Some(binding),
            ..
        } => rewrite_pattern_spans(binding, fallback_span, source_map),
        Pattern::Record { fields, rest } => {
            for (_, _, binding_span) in fields {
                *binding_span = expanded_ast_span(*binding_span, fallback_span, source_map);
            }
            if let Some(Some((_, binding_span))) = rest {
                *binding_span = expanded_ast_span(*binding_span, fallback_span, source_map);
            }
        }
        Pattern::List { elements, rest } => {
            for element in elements {
                rewrite_pattern_spans(element, fallback_span, source_map);
            }
            if let Some(Some((_, binding_span))) = rest {
                *binding_span = expanded_ast_span(*binding_span, fallback_span, source_map);
            }
        }
        Pattern::Tuple(items) => {
            for item in items {
                rewrite_pattern_spans(item, fallback_span, source_map);
            }
        }
        Pattern::Wildcard
        | Pattern::StringLit(_)
        | Pattern::NumberLit(_)
        | Pattern::BoolLit(_)
        | Pattern::IntRange { .. }
        | Pattern::Constructor { binding: None, .. }
        | Pattern::SyntaxQuote(_) => {}
    }
}
