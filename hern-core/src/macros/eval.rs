use crate::ast::{Pattern, SourceSpan, Stmt, Type};
use crate::lex::Lexer;
use crate::parse::Parser;
use crate::syntax::{Syntax, SyntaxDelimiter, SyntaxKind, SyntaxToken, syntax_nodes_to_source};
use std::collections::{HashMap, HashSet};

use super::core_ir::{
    CoreAssignTarget, CoreCallee, CoreExpr, CoreExprKind, CoreFunction, CoreIntrinsic, CoreStmt,
    CoreStmtKind,
};
use super::diagnostics::{MacroRuntimeError, pattern_span};
use super::pattern::match_macro_pattern;
use super::runtime::MacroRuntimeState;
use super::source::{
    fresh_token_syntax, generated_token_syntax, generated_tree_syntax, sequence_syntax,
    syntax_at_use_site, syntax_debug, syntax_shape_eq, syntax_token_source, use_site_token_syntax,
};
use super::template::expand_template;
use super::value::{MacroEnv, MacroValue, macro_value_eq, macro_value_to_string};

pub(super) fn eval_macro_result(
    expr: &CoreExpr,
    param_name: &str,
    input: Syntax,
    call_span: SourceSpan,
    state: &mut MacroRuntimeState,
    helpers: &HashMap<String, Result<CoreFunction, MacroRuntimeError>>,
) -> Result<Syntax, MacroRuntimeError> {
    let mut env = MacroEnv::new();
    env.insert(
        param_name.to_string(),
        MacroValue::Syntax(syntax_at_use_site(input, call_span)),
    );
    match eval_expr(expr, &mut env, state, helpers)? {
        MacroValue::ResultOk(value) => match *value {
            MacroValue::Syntax(syntax) => Ok(syntax),
            _ => Err(MacroRuntimeError::new(
                call_span,
                "macro returned Ok with a non-Syntax value",
            )),
        },
        MacroValue::ResultErr(message) => Err(MacroRuntimeError::new(call_span, message)),
        MacroValue::Break(_) => Err(MacroRuntimeError::new(
            call_span,
            "break outside macro loop",
        )),
        _ => Err(MacroRuntimeError::new(
            call_span,
            "macro must return MacroResult(Syntax)",
        )),
    }
}

pub(super) fn eval_expr(
    expr: &CoreExpr,
    env: &mut MacroEnv,
    state: &mut MacroRuntimeState,
    helpers: &HashMap<String, Result<CoreFunction, MacroRuntimeError>>,
) -> Result<MacroValue, MacroRuntimeError> {
    state.spend(expr.span)?;
    match &expr.kind {
        CoreExprKind::Unit => Ok(MacroValue::Unit),
        CoreExprKind::Int(value) => Ok(MacroValue::Int(*value)),
        CoreExprKind::Float(value) => Ok(MacroValue::Float(*value)),
        CoreExprKind::Bool(value) => Ok(MacroValue::Bool(*value)),
        CoreExprKind::String(value) => Ok(MacroValue::String(value.clone())),
        CoreExprKind::Ident(name) => env
            .get(name)
            .cloned()
            .or_else(|| syntax_delimiter_ident_value(name))
            .ok_or_else(|| {
                MacroRuntimeError::new(expr.span, format!("unknown macro-phase binding `{name}`"))
            }),
        CoreExprKind::SyntaxQuote(template) => {
            expand_template(template, env, state).map(MacroValue::Syntax)
        }
        CoreExprKind::Lambda { params, body } => Ok(MacroValue::Closure(
            CoreFunction {
                params: params.clone(),
                body: (**body).clone(),
            },
            env.clone(),
        )),
        CoreExprKind::Grouped(inner) => eval_expr(inner, env, state, helpers),
        CoreExprKind::If {
            cond,
            then_branch,
            else_branch,
        } => {
            let cond_span = cond.span;
            let cond = eval_expr(cond, env, state, helpers)?;
            if matches!(cond, MacroValue::Break(_)) {
                return Ok(cond);
            }
            match cond {
                MacroValue::Bool(true) => eval_expr(then_branch, env, state, helpers),
                MacroValue::Bool(false) => eval_expr(else_branch, env, state, helpers),
                _ => Err(MacroRuntimeError::new(
                    cond_span,
                    "if condition expects bool",
                )),
            }
        }
        CoreExprKind::Block { stmts, final_expr } => {
            let original_bindings = env.clone();
            let mut local_bindings = HashSet::new();
            for stmt in stmts {
                if let Some(value) = eval_stmt(stmt, env, &mut local_bindings, state, helpers)? {
                    discard_block_locals(env, &original_bindings, &local_bindings);
                    return Ok(value);
                }
            }
            let result = final_expr
                .as_deref()
                .map(|expr| eval_expr(expr, env, state, helpers))
                .unwrap_or(Ok(MacroValue::Unit));
            discard_block_locals(env, &original_bindings, &local_bindings);
            result
        }
        CoreExprKind::Loop(body) => loop {
            if let MacroValue::Break(value) = eval_expr(body, env, state, helpers)? {
                break Ok(*value);
            }
        },
        CoreExprKind::Break(value) => {
            let value = value
                .as_deref()
                .map(|value| eval_expr(value, env, state, helpers))
                .unwrap_or(Ok(MacroValue::Unit))?;
            Ok(MacroValue::Break(Box::new(value)))
        }
        CoreExprKind::Assign { target, value } => {
            let value = eval_expr(value, env, state, helpers)?;
            if matches!(value, MacroValue::Break(_)) {
                return Ok(value);
            }
            match target {
                CoreAssignTarget::Ident(name) => {
                    if !env.contains_key(name) {
                        return Err(MacroRuntimeError::new(
                            expr.span,
                            format!("unknown macro-phase binding `{name}`"),
                        ));
                    }
                    env.insert(name.clone(), value);
                    Ok(MacroValue::Unit)
                }
                CoreAssignTarget::Unsupported(span) => Err(MacroRuntimeError::new(
                    *span,
                    "unsupported assignment target in macro body",
                )),
            }
        }
        CoreExprKind::Match { scrutinee, arms } => {
            let value = eval_expr(scrutinee, env, state, helpers)?;
            if matches!(value, MacroValue::Break(_)) {
                return Ok(value);
            }
            for (pattern, body) in arms {
                let mut scoped = env.clone();
                if match_macro_pattern(pattern, &value, &mut scoped)? {
                    return eval_expr(body, &mut scoped, state, helpers);
                }
            }
            let arm_span = arms
                .iter()
                .map(|(pattern, _)| pattern_span(pattern))
                .find(|span| !span.is_synthetic())
                .unwrap_or(expr.span);
            let mut error = MacroRuntimeError::new(expr.span, "non-exhaustive macro match");
            if !arm_span.is_synthetic() {
                error = error.with_related(arm_span, "relevant macro pattern arm is here");
            }
            Err(error)
        }
        CoreExprKind::Call { callee, args } => {
            eval_macro_call(expr.span, callee, args, env, state, helpers)
        }
        CoreExprKind::Array(items) => {
            let mut values = Vec::with_capacity(items.len());
            for item in items {
                let value = eval_expr(item, env, state, helpers)?;
                if matches!(value, MacroValue::Break(_)) {
                    return Ok(value);
                }
                values.push(value);
            }
            Ok(MacroValue::Array(values))
        }
        CoreExprKind::Tuple(items) => {
            let mut values = Vec::with_capacity(items.len());
            for item in items {
                let value = eval_expr(item, env, state, helpers)?;
                if matches!(value, MacroValue::Break(_)) {
                    return Ok(value);
                }
                values.push(value);
            }
            Ok(MacroValue::Tuple(values))
        }
        CoreExprKind::Record(entries) => {
            let mut values = Vec::with_capacity(entries.len());
            for (field, expr) in entries {
                let value = eval_expr(expr, env, state, helpers)?;
                if matches!(value, MacroValue::Break(_)) {
                    return Ok(value);
                }
                values.push((field.clone(), value));
            }
            Ok(MacroValue::Record(values))
        }
        CoreExprKind::FieldAccess {
            receiver,
            field,
            field_span,
        } => {
            let receiver = eval_expr(receiver, env, state, helpers)?;
            if matches!(receiver, MacroValue::Break(_)) {
                return Ok(receiver);
            }
            eval_field_access(*field_span, receiver, field)
        }
        CoreExprKind::Index { receiver, key } => {
            let receiver = eval_expr(receiver, env, state, helpers)?;
            if matches!(receiver, MacroValue::Break(_)) {
                return Ok(receiver);
            }
            let key = eval_expr(key, env, state, helpers)?;
            if matches!(key, MacroValue::Break(_)) {
                return Ok(key);
            }
            eval_index(expr.span, receiver, key)
        }
    }
}

fn eval_stmt(
    stmt: &CoreStmt,
    env: &mut MacroEnv,
    local_bindings: &mut HashSet<String>,
    state: &mut MacroRuntimeState,
    helpers: &HashMap<String, Result<CoreFunction, MacroRuntimeError>>,
) -> Result<Option<MacroValue>, MacroRuntimeError> {
    state.spend(stmt.span)?;
    match stmt {
        CoreStmt {
            kind: CoreStmtKind::Let { pat, value },
            ..
        } => {
            let value = eval_expr(value, env, state, helpers)?;
            if matches!(value, MacroValue::Break(_)) {
                return Ok(Some(value));
            }
            record_runtime_pattern_bindings(pat, local_bindings);
            bind_runtime_pattern(pat, value, env)?;
            Ok(None)
        }
        CoreStmt {
            kind: CoreStmtKind::Expr(expr),
            ..
        } => {
            let value = eval_expr(expr, env, state, helpers)?;
            if matches!(value, MacroValue::Break(_)) {
                Ok(Some(value))
            } else {
                Ok(None)
            }
        }
    }
}

fn discard_block_locals(
    env: &mut MacroEnv,
    original_bindings: &MacroEnv,
    local_bindings: &HashSet<String>,
) {
    for name in local_bindings {
        env.remove(name);
        if let Some(value) = original_bindings.get(name) {
            env.insert(name.clone(), value.clone());
        }
    }
}

fn record_runtime_pattern_bindings(pattern: &Pattern, local_bindings: &mut HashSet<String>) {
    match pattern {
        Pattern::Variable(name, _) => {
            local_bindings.insert(name.clone());
        }
        Pattern::Constructor {
            binding: Some(binding),
            ..
        } => record_runtime_pattern_bindings(binding, local_bindings),
        Pattern::Tuple(items)
        | Pattern::List {
            elements: items, ..
        } => {
            for item in items {
                record_runtime_pattern_bindings(item, local_bindings);
            }
        }
        Pattern::Record { fields, rest } => {
            for (_, binding, _) in fields {
                local_bindings.insert(binding.clone());
            }
            if let Some(Some((binding, _))) = rest {
                local_bindings.insert(binding.clone());
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

fn eval_macro_call(
    span: SourceSpan,
    callee: &CoreCallee,
    args: &[CoreExpr],
    env: &mut MacroEnv,
    state: &mut MacroRuntimeState,
    helpers: &HashMap<String, Result<CoreFunction, MacroRuntimeError>>,
) -> Result<MacroValue, MacroRuntimeError> {
    let name = match callee {
        CoreCallee::Ident(name) => name,
        CoreCallee::Intrinsic(intrinsic) => {
            return eval_intrinsic_call(span, *intrinsic, args, env, state, helpers);
        }
        CoreCallee::Expr(expr) => {
            let value = eval_expr(expr, env, state, helpers)?;
            if matches!(value, MacroValue::Break(_)) {
                return Ok(value);
            }
            return eval_macro_callable(span, value, args, env, state, helpers);
        }
        CoreCallee::Method {
            receiver,
            name,
            span,
        } => return eval_macro_method_call(span, receiver, name, args, env, state, helpers),
    };
    match name.as_str() {
        "Keyword" | "Literal" | "Operator" | "Punct" if args.len() == 1 => {
            let value = eval_expr(&args[0], env, state, helpers)?;
            if matches!(value, MacroValue::Break(_)) {
                return Ok(value);
            }
            match value {
                MacroValue::String(text) => Ok(MacroValue::Variant(
                    name.to_string(),
                    Some(Box::new(MacroValue::String(text))),
                )),
                _ => Err(MacroRuntimeError::new(
                    args[0].span,
                    format!("{name} expects a string"),
                )),
            }
        }
        "Ok" if args.len() == 1 => {
            let value = eval_expr(&args[0], env, state, helpers)?;
            if matches!(value, MacroValue::Break(_)) {
                return Ok(value);
            }
            Ok(MacroValue::ResultOk(Box::new(value)))
        }
        "Err" if args.len() == 1 => {
            let value = eval_expr(&args[0], env, state, helpers)?;
            if matches!(value, MacroValue::Break(_)) {
                return Ok(value);
            }
            match value {
                MacroValue::Error(message) => Ok(MacroValue::ResultErr(message)),
                _ => Err(MacroRuntimeError::new(
                    args[0].span,
                    "Err expects MacroError",
                )),
            }
        }
        "MacroError" if args.len() == 1 => {
            let value = eval_expr(&args[0], env, state, helpers)?;
            if matches!(value, MacroValue::Break(_)) {
                return Ok(value);
            }
            match value {
                MacroValue::String(message) => Ok(MacroValue::Error(message)),
                _ => Err(MacroRuntimeError::new(
                    args[0].span,
                    "MacroError expects a string",
                )),
            }
        }
        "syntax_children" if args.len() == 1 => {
            let value = eval_expr(&args[0], env, state, helpers)?;
            if matches!(value, MacroValue::Break(_)) {
                return Ok(value);
            }
            match value {
                MacroValue::Syntax(syntax) => match syntax.kind {
                    crate::syntax::SyntaxKind::Tree { children, .. }
                    | crate::syntax::SyntaxKind::Sequence(children) => {
                        Ok(MacroValue::SyntaxArray(children))
                    }
                    crate::syntax::SyntaxKind::Token(_) => Ok(MacroValue::SyntaxArray(Vec::new())),
                },
                _ => Err(MacroRuntimeError::new(
                    args[0].span,
                    "syntax_children expects Syntax",
                )),
            }
        }
        "syntax_delimiter" if args.len() == 1 => {
            let value = eval_expr(&args[0], env, state, helpers)?;
            if matches!(value, MacroValue::Break(_)) {
                return Ok(value);
            }
            match value {
                MacroValue::Syntax(syntax) => match syntax.kind {
                    crate::syntax::SyntaxKind::Tree { delimiter, .. } => Ok(
                        MacroValue::OptionSome(Box::new(syntax_delimiter_value(delimiter))),
                    ),
                    _ => Ok(MacroValue::OptionNone),
                },
                _ => Err(MacroRuntimeError::new(
                    args[0].span,
                    "syntax_delimiter expects Syntax",
                )),
            }
        }
        "syntax_kind" if args.len() == 1 => {
            let value = eval_expr(&args[0], env, state, helpers)?;
            if matches!(value, MacroValue::Break(_)) {
                return Ok(value);
            }
            match value {
                MacroValue::Syntax(syntax) => Ok(syntax_kind_value(&syntax)),
                _ => Err(MacroRuntimeError::new(
                    args[0].span,
                    "syntax_kind expects Syntax",
                )),
            }
        }
        "syntax_span" if args.len() == 1 => {
            let value = eval_expr(&args[0], env, state, helpers)?;
            if matches!(value, MacroValue::Break(_)) {
                return Ok(value);
            }
            match value {
                MacroValue::Syntax(syntax) => Ok(syntax_span_value(syntax.span)),
                _ => Err(MacroRuntimeError::new(
                    args[0].span,
                    "syntax_span expects Syntax",
                )),
            }
        }
        "syntax_origin" if args.len() == 1 => {
            let value = eval_expr(&args[0], env, state, helpers)?;
            if matches!(value, MacroValue::Break(_)) {
                return Ok(value);
            }
            match value {
                MacroValue::Syntax(syntax) => Ok(syntax_origin_value(&syntax.origin)),
                _ => Err(MacroRuntimeError::new(
                    args[0].span,
                    "syntax_origin expects Syntax",
                )),
            }
        }
        "syntax_token_text" if args.len() == 1 => {
            let value = eval_expr(&args[0], env, state, helpers)?;
            if matches!(value, MacroValue::Break(_)) {
                return Ok(value);
            }
            match value {
                MacroValue::Syntax(syntax) => match syntax.kind {
                    crate::syntax::SyntaxKind::Token(token) => Ok(MacroValue::OptionSome(
                        Box::new(MacroValue::String(syntax_token_source(&token))),
                    )),
                    _ => Ok(MacroValue::OptionNone),
                },
                _ => Err(MacroRuntimeError::new(
                    args[0].span,
                    "syntax_token_text expects Syntax",
                )),
            }
        }
        "syntax_is_ident" if args.len() == 2 => {
            let syntax = eval_expr(&args[0], env, state, helpers)?;
            if matches!(syntax, MacroValue::Break(_)) {
                return Ok(syntax);
            }
            let name = eval_expr(&args[1], env, state, helpers)?;
            if matches!(name, MacroValue::Break(_)) {
                return Ok(name);
            }
            match (syntax, name) {
                (
                    MacroValue::Syntax(Syntax {
                        kind:
                            crate::syntax::SyntaxKind::Token(crate::syntax::SyntaxToken::Ident(actual)),
                        ..
                    }),
                    MacroValue::String(name),
                ) => Ok(MacroValue::Bool(actual == name)),
                (MacroValue::Syntax(_), MacroValue::String(_)) => Ok(MacroValue::Bool(false)),
                _ => Err(MacroRuntimeError::new(
                    span,
                    "syntax_is_ident expects Syntax and string",
                )),
            }
        }
        "syntax_eq_shape" if args.len() == 2 => {
            let lhs = eval_expr(&args[0], env, state, helpers)?;
            if matches!(lhs, MacroValue::Break(_)) {
                return Ok(lhs);
            }
            let rhs = eval_expr(&args[1], env, state, helpers)?;
            if matches!(rhs, MacroValue::Break(_)) {
                return Ok(rhs);
            }
            match (lhs, rhs) {
                (MacroValue::Syntax(lhs), MacroValue::Syntax(rhs)) => {
                    Ok(MacroValue::Bool(syntax_shape_eq(&lhs, &rhs)))
                }
                _ => Err(MacroRuntimeError::new(
                    span,
                    "syntax_eq_shape expects Syntax and Syntax",
                )),
            }
        }
        "syntax_same_binding" if args.len() == 2 => {
            let lhs = eval_expr(&args[0], env, state, helpers)?;
            if matches!(lhs, MacroValue::Break(_)) {
                return Ok(lhs);
            }
            let rhs = eval_expr(&args[1], env, state, helpers)?;
            if matches!(rhs, MacroValue::Break(_)) {
                return Ok(rhs);
            }
            match (lhs, rhs) {
                (
                    MacroValue::Syntax(Syntax {
                        kind:
                            crate::syntax::SyntaxKind::Token(crate::syntax::SyntaxToken::Ident(
                                lhs_name,
                            )),
                        scopes: lhs_scopes,
                        ..
                    }),
                    MacroValue::Syntax(Syntax {
                        kind:
                            crate::syntax::SyntaxKind::Token(crate::syntax::SyntaxToken::Ident(
                                rhs_name,
                            )),
                        scopes: rhs_scopes,
                        ..
                    }),
                ) => Ok(MacroValue::Bool(
                    lhs_name == rhs_name && lhs_scopes == rhs_scopes,
                )),
                (MacroValue::Syntax(_), MacroValue::Syntax(_)) => Ok(MacroValue::Bool(false)),
                _ => Err(MacroRuntimeError::new(
                    span,
                    "syntax_same_binding expects Syntax and Syntax",
                )),
            }
        }
        "syntax_token" if args.len() == 1 => {
            let value = eval_expr(&args[0], env, state, helpers)?;
            if matches!(value, MacroValue::Break(_)) {
                return Ok(value);
            }
            match value {
                MacroValue::Variant(name, payload) => {
                    let token = macro_value_to_syntax_token(span, &name, payload.as_deref())?;
                    Ok(MacroValue::Syntax(generated_token_syntax(token)))
                }
                _ => Err(MacroRuntimeError::new(
                    args[0].span,
                    "syntax_token expects SyntaxToken",
                )),
            }
        }
        "syntax_tree" if args.len() == 2 => {
            let delimiter = eval_expr(&args[0], env, state, helpers)?;
            if matches!(delimiter, MacroValue::Break(_)) {
                return Ok(delimiter);
            }
            let children = eval_expr(&args[1], env, state, helpers)?;
            if matches!(children, MacroValue::Break(_)) {
                return Ok(children);
            }
            let delimiter = macro_value_to_syntax_delimiter(span, delimiter)?;
            let children = macro_value_to_syntax_vec(span, children)?;
            Ok(MacroValue::Syntax(generated_tree_syntax(
                delimiter, children,
            )))
        }
        "syntax_sequence" if args.len() == 1 => {
            let children = eval_expr(&args[0], env, state, helpers)?;
            if matches!(children, MacroValue::Break(_)) {
                return Ok(children);
            }
            Ok(MacroValue::Syntax(sequence_syntax(
                macro_value_to_syntax_vec(span, children)?,
            )))
        }
        "syntax_ident" if args.len() == 1 => eval_syntax_token_constructor(
            "syntax_ident",
            SyntaxTokenConstructor::Ident,
            &args[0],
            env,
            state,
            helpers,
        ),
        "syntax_literal" if args.len() == 1 => eval_syntax_token_constructor(
            "syntax_literal",
            SyntaxTokenConstructor::Literal,
            &args[0],
            env,
            state,
            helpers,
        ),
        "syntax_operator" if args.len() == 1 => eval_syntax_token_constructor(
            "syntax_operator",
            SyntaxTokenConstructor::Operator,
            &args[0],
            env,
            state,
            helpers,
        ),
        "syntax_punct" if args.len() == 1 => eval_syntax_token_constructor(
            "syntax_punct",
            SyntaxTokenConstructor::Punct,
            &args[0],
            env,
            state,
            helpers,
        ),
        "syntax_fresh_ident" if args.len() == 1 => {
            let value = eval_expr(&args[0], env, state, helpers)?;
            if matches!(value, MacroValue::Break(_)) {
                return Ok(value);
            }
            let MacroValue::String(text) = value else {
                return Err(MacroRuntimeError::new(
                    args[0].span,
                    "syntax_fresh_ident expects a string",
                ));
            };
            Ok(MacroValue::Syntax(fresh_token_syntax(
                SyntaxToken::Ident(text),
                state.fresh_scope_id(),
            )))
        }
        "syntax_ident_at_use_site" if args.len() == 1 => {
            let value = eval_expr(&args[0], env, state, helpers)?;
            if matches!(value, MacroValue::Break(_)) {
                return Ok(value);
            }
            let MacroValue::String(text) = value else {
                return Err(MacroRuntimeError::new(
                    args[0].span,
                    "syntax_ident_at_use_site expects a string",
                ));
            };
            Ok(MacroValue::Syntax(use_site_token_syntax(
                SyntaxToken::Ident(text),
                state.macro_call_span(),
            )))
        }
        "syntax_map_children" if args.len() == 2 => {
            let syntax = eval_expr(&args[0], env, state, helpers)?;
            if matches!(syntax, MacroValue::Break(_)) {
                return Ok(syntax);
            }
            let mapper = eval_expr(&args[1], env, state, helpers)?;
            if matches!(mapper, MacroValue::Break(_)) {
                return Ok(mapper);
            }
            match syntax {
                MacroValue::Syntax(syntax) => {
                    syntax_map_children(span, syntax, mapper, env, state, helpers)
                        .map(MacroValue::Syntax)
                }
                _ => Err(MacroRuntimeError::new(
                    args[0].span,
                    "syntax_map_children expects Syntax and fn(Syntax) -> Syntax",
                )),
            }
        }
        "syntax_find" if args.len() == 2 => {
            let syntax = eval_expr(&args[0], env, state, helpers)?;
            if matches!(syntax, MacroValue::Break(_)) {
                return Ok(syntax);
            }
            let predicate = eval_expr(&args[1], env, state, helpers)?;
            if matches!(predicate, MacroValue::Break(_)) {
                return Ok(predicate);
            }
            match syntax {
                MacroValue::Syntax(syntax) => {
                    match syntax_find(span, &syntax, predicate, env, state, helpers)? {
                        Some(found) => {
                            Ok(MacroValue::OptionSome(Box::new(MacroValue::Syntax(found))))
                        }
                        None => Ok(MacroValue::OptionNone),
                    }
                }
                _ => Err(MacroRuntimeError::new(
                    args[0].span,
                    "syntax_find expects Syntax and fn(Syntax) -> bool",
                )),
            }
        }
        "syntax_replace" if args.len() == 3 => {
            let syntax = eval_expr(&args[0], env, state, helpers)?;
            if matches!(syntax, MacroValue::Break(_)) {
                return Ok(syntax);
            }
            let target = eval_expr(&args[1], env, state, helpers)?;
            if matches!(target, MacroValue::Break(_)) {
                return Ok(target);
            }
            let replacement = eval_expr(&args[2], env, state, helpers)?;
            if matches!(replacement, MacroValue::Break(_)) {
                return Ok(replacement);
            }
            match (syntax, target, replacement) {
                (
                    MacroValue::Syntax(syntax),
                    MacroValue::Syntax(target),
                    MacroValue::Syntax(replacement),
                ) => Ok(MacroValue::Syntax(syntax_replace(
                    syntax,
                    &target,
                    &replacement,
                ))),
                _ => Err(MacroRuntimeError::new(
                    span,
                    "syntax_replace expects Syntax, Syntax, and Syntax",
                )),
            }
        }
        "syntax_join" if args.len() == 2 => {
            let items = eval_expr(&args[0], env, state, helpers)?;
            if matches!(items, MacroValue::Break(_)) {
                return Ok(items);
            }
            let separator = eval_expr(&args[1], env, state, helpers)?;
            if matches!(separator, MacroValue::Break(_)) {
                return Ok(separator);
            }
            let items = macro_value_to_syntax_vec(span, items)?;
            let MacroValue::Syntax(separator) = separator else {
                return Err(MacroRuntimeError::new(
                    args[1].span,
                    "syntax_join expects [Syntax] and Syntax",
                ));
            };
            Ok(MacroValue::Syntax(sequence_syntax(syntax_join(
                items, separator,
            ))))
        }
        "syntax_debug" if args.len() == 1 => {
            let value = eval_expr(&args[0], env, state, helpers)?;
            if matches!(value, MacroValue::Break(_)) {
                return Ok(value);
            }
            match value {
                MacroValue::Syntax(syntax) => Ok(MacroValue::String(syntax_debug(&syntax))),
                _ => Err(MacroRuntimeError::new(
                    args[0].span,
                    "syntax_debug expects Syntax",
                )),
            }
        }
        "macro_resolve_ident" if args.len() == 1 => {
            let value = eval_expr(&args[0], env, state, helpers)?;
            if matches!(value, MacroValue::Break(_)) {
                return Ok(value);
            }
            match value {
                MacroValue::Syntax(syntax) => Ok(macro_option_string(reflect_ident(&syntax))),
                _ => Err(MacroRuntimeError::new(
                    args[0].span,
                    "macro_resolve_ident expects Syntax",
                )),
            }
        }
        "macro_type_of" if args.len() == 1 => {
            let value = eval_expr(&args[0], env, state, helpers)?;
            if matches!(value, MacroValue::Break(_)) {
                return Ok(value);
            }
            match value {
                MacroValue::Syntax(syntax) => Ok(macro_option_string(reflect_type_of(&syntax))),
                _ => Err(MacroRuntimeError::new(
                    args[0].span,
                    "macro_type_of expects Syntax",
                )),
            }
        }
        "macro_fields_of" if args.len() == 1 => {
            let value = eval_expr(&args[0], env, state, helpers)?;
            if matches!(value, MacroValue::Break(_)) {
                return Ok(value);
            }
            match value {
                MacroValue::Syntax(syntax) => Ok(macro_string_array(reflect_fields(&syntax))),
                _ => Err(MacroRuntimeError::new(
                    args[0].span,
                    "macro_fields_of expects Syntax",
                )),
            }
        }
        "macro_variants_of" if args.len() == 1 => {
            let value = eval_expr(&args[0], env, state, helpers)?;
            if matches!(value, MacroValue::Break(_)) {
                return Ok(value);
            }
            match value {
                MacroValue::Syntax(syntax) => {
                    let program = reflect_program(args[0].span, &syntax)?;
                    Ok(macro_string_array(
                        program
                            .stmts
                            .iter()
                            .find_map(|stmt| match stmt {
                                Stmt::Type(type_def) => Some(
                                    type_def
                                        .variants
                                        .iter()
                                        .map(|variant| variant.name.clone())
                                        .collect(),
                                ),
                                _ => None,
                            })
                            .unwrap_or_default(),
                    ))
                }
                _ => Err(MacroRuntimeError::new(
                    args[0].span,
                    "macro_variants_of expects Syntax",
                )),
            }
        }
        "macro_trait_methods_of" if args.len() == 1 => {
            let value = eval_expr(&args[0], env, state, helpers)?;
            if matches!(value, MacroValue::Break(_)) {
                return Ok(value);
            }
            match value {
                MacroValue::Syntax(syntax) => {
                    let program = reflect_program(args[0].span, &syntax)?;
                    Ok(macro_string_array(
                        program
                            .stmts
                            .iter()
                            .find_map(|stmt| match stmt {
                                Stmt::Trait(trait_def) => Some(
                                    trait_def
                                        .methods
                                        .iter()
                                        .map(|method| method.name.clone())
                                        .collect(),
                                ),
                                _ => None,
                            })
                            .unwrap_or_default(),
                    ))
                }
                _ => Err(MacroRuntimeError::new(
                    args[0].span,
                    "macro_trait_methods_of expects Syntax",
                )),
            }
        }
        "macro_module_items" if args.len() == 1 => {
            let value = eval_expr(&args[0], env, state, helpers)?;
            if matches!(value, MacroValue::Break(_)) {
                return Ok(value);
            }
            match value {
                MacroValue::Syntax(syntax) => {
                    let program = reflect_program(args[0].span, &syntax)?;
                    Ok(macro_string_array(
                        program.stmts.iter().filter_map(stmt_item_name).collect(),
                    ))
                }
                _ => Err(MacroRuntimeError::new(
                    args[0].span,
                    "macro_module_items expects Syntax",
                )),
            }
        }
        "to_string" if args.len() == 1 => {
            let value = eval_expr(&args[0], env, state, helpers)?;
            if matches!(value, MacroValue::Break(_)) {
                return Ok(value);
            }
            Ok(MacroValue::String(macro_value_to_string(&value)))
        }
        _ if env.contains_key(name) => {
            let value = env.get(name).cloned().expect("checked env contains key");
            eval_macro_callable(span, value, args, env, state, helpers)
        }
        _ if helpers.contains_key(name) => eval_helper_call(span, name, args, env, state, helpers),
        _ => Err(MacroRuntimeError::new(
            span,
            format!("unsupported macro-phase call `{name}`"),
        )),
    }
}

fn eval_macro_callable_value(
    span: SourceSpan,
    callable: MacroValue,
    values: Vec<MacroValue>,
    state: &mut MacroRuntimeState,
    helpers: &HashMap<String, Result<CoreFunction, MacroRuntimeError>>,
) -> Result<MacroValue, MacroRuntimeError> {
    match callable {
        MacroValue::Closure(function, mut callee_env) => {
            if values.len() != function.params.len() {
                return Err(MacroRuntimeError::new(
                    span,
                    format!(
                        "wrong number of macro-phase function arguments: expected {}, got {}",
                        function.params.len(),
                        values.len()
                    ),
                ));
            }
            state.enter_call(span)?;
            let result = (|| {
                for (pattern, value) in function.params.iter().zip(values) {
                    bind_runtime_pattern(pattern, value, &mut callee_env)?;
                }
                eval_expr(&function.body, &mut callee_env, state, helpers)
            })();
            state.exit_call();
            result
        }
        _ => Err(MacroRuntimeError::new(
            span,
            "macro-phase helper expects a function",
        )),
    }
}

fn syntax_map_children(
    span: SourceSpan,
    mut syntax: Syntax,
    mapper: MacroValue,
    env: &mut MacroEnv,
    state: &mut MacroRuntimeState,
    helpers: &HashMap<String, Result<CoreFunction, MacroRuntimeError>>,
) -> Result<Syntax, MacroRuntimeError> {
    let children = match &mut syntax.kind {
        crate::syntax::SyntaxKind::Tree { children, .. }
        | crate::syntax::SyntaxKind::Sequence(children) => children,
        crate::syntax::SyntaxKind::Token(_) => return Ok(syntax),
    };
    let mut mapped = Vec::with_capacity(children.len());
    for child in children.iter().cloned() {
        match eval_macro_callable_value(
            span,
            mapper.clone(),
            vec![MacroValue::Syntax(child)],
            state,
            helpers,
        )? {
            MacroValue::Syntax(value) => mapped.push(value),
            MacroValue::Break(value) => {
                return Err(MacroRuntimeError::new(
                    span,
                    format!(
                        "syntax_map_children mapper cannot break with {}",
                        macro_value_to_string(&value)
                    ),
                ));
            }
            _ => {
                return Err(MacroRuntimeError::new(
                    span,
                    "syntax_map_children mapper must return Syntax",
                ));
            }
        }
    }
    let _ = env;
    *children = mapped;
    Ok(syntax)
}

fn syntax_find(
    span: SourceSpan,
    syntax: &Syntax,
    predicate: MacroValue,
    env: &mut MacroEnv,
    state: &mut MacroRuntimeState,
    helpers: &HashMap<String, Result<CoreFunction, MacroRuntimeError>>,
) -> Result<Option<Syntax>, MacroRuntimeError> {
    match eval_macro_callable_value(
        span,
        predicate.clone(),
        vec![MacroValue::Syntax(syntax.clone())],
        state,
        helpers,
    )? {
        MacroValue::Bool(true) => return Ok(Some(syntax.clone())),
        MacroValue::Bool(false) => {}
        MacroValue::Break(value) => {
            return Err(MacroRuntimeError::new(
                span,
                format!(
                    "syntax_find predicate cannot break with {}",
                    macro_value_to_string(&value)
                ),
            ));
        }
        _ => {
            return Err(MacroRuntimeError::new(
                span,
                "syntax_find predicate must return bool",
            ));
        }
    }
    let children = match &syntax.kind {
        crate::syntax::SyntaxKind::Tree { children, .. }
        | crate::syntax::SyntaxKind::Sequence(children) => children,
        crate::syntax::SyntaxKind::Token(_) => return Ok(None),
    };
    for child in children {
        if let Some(found) = syntax_find(span, child, predicate.clone(), env, state, helpers)? {
            return Ok(Some(found));
        }
    }
    let _ = env;
    Ok(None)
}

fn syntax_replace(syntax: Syntax, target: &Syntax, replacement: &Syntax) -> Syntax {
    if syntax_shape_eq(&syntax, target) {
        return replacement.clone();
    }
    match syntax.kind {
        crate::syntax::SyntaxKind::Tree {
            delimiter,
            children,
        } => Syntax {
            kind: crate::syntax::SyntaxKind::Tree {
                delimiter,
                children: children
                    .into_iter()
                    .map(|child| syntax_replace(child, target, replacement))
                    .collect(),
            },
            ..syntax
        },
        crate::syntax::SyntaxKind::Sequence(children) => Syntax {
            kind: crate::syntax::SyntaxKind::Sequence(
                children
                    .into_iter()
                    .map(|child| syntax_replace(child, target, replacement))
                    .collect(),
            ),
            ..syntax
        },
        crate::syntax::SyntaxKind::Token(_) => syntax,
    }
}

fn syntax_join(items: Vec<Syntax>, separator: Syntax) -> Vec<Syntax> {
    let mut out = Vec::with_capacity(items.len().saturating_mul(2).saturating_sub(1));
    let mut first = true;
    for item in items {
        if first {
            first = false;
        } else {
            out.push(separator.clone());
        }
        out.push(item);
    }
    out
}

fn eval_macro_callable(
    span: SourceSpan,
    callable: MacroValue,
    args: &[CoreExpr],
    env: &mut MacroEnv,
    state: &mut MacroRuntimeState,
    helpers: &HashMap<String, Result<CoreFunction, MacroRuntimeError>>,
) -> Result<MacroValue, MacroRuntimeError> {
    match callable {
        MacroValue::Closure(function, captured_env) => {
            eval_function_call(span, &function, args, env, captured_env, state, helpers)
        }
        _ => Err(MacroRuntimeError::new(
            span,
            "macro-phase call expects a function",
        )),
    }
}

#[derive(Debug, Clone, Copy)]
enum SyntaxTokenConstructor {
    Ident,
    Literal,
    Operator,
    Punct,
}

fn eval_syntax_token_constructor(
    name: &str,
    constructor: SyntaxTokenConstructor,
    arg: &CoreExpr,
    env: &mut MacroEnv,
    state: &mut MacroRuntimeState,
    helpers: &HashMap<String, Result<CoreFunction, MacroRuntimeError>>,
) -> Result<MacroValue, MacroRuntimeError> {
    let value = eval_expr(arg, env, state, helpers)?;
    if matches!(value, MacroValue::Break(_)) {
        return Ok(value);
    }
    let MacroValue::String(text) = value else {
        return Err(MacroRuntimeError::new(
            arg.span,
            format!("{name} expects a string"),
        ));
    };
    let token = match constructor {
        SyntaxTokenConstructor::Ident => SyntaxToken::Ident(text),
        SyntaxTokenConstructor::Literal => SyntaxToken::Literal(text),
        SyntaxTokenConstructor::Operator => SyntaxToken::Operator(text),
        SyntaxTokenConstructor::Punct => SyntaxToken::Punct(text),
    };
    Ok(MacroValue::Syntax(generated_token_syntax(token)))
}

fn macro_option_string(value: Option<String>) -> MacroValue {
    value
        .map(|value| MacroValue::OptionSome(Box::new(MacroValue::String(value))))
        .unwrap_or(MacroValue::OptionNone)
}

fn macro_string_array(values: Vec<String>) -> MacroValue {
    MacroValue::Array(values.into_iter().map(MacroValue::String).collect())
}

fn reflection_source(syntax: &Syntax) -> String {
    match &syntax.kind {
        SyntaxKind::Tree {
            delimiter: SyntaxDelimiter::Paren,
            children,
        } if children.len() == 1 => reflection_source(&children[0]),
        SyntaxKind::Tree {
            delimiter: SyntaxDelimiter::Brace,
            children,
        }
        | SyntaxKind::Sequence(children) => syntax_nodes_to_source(children),
        _ => crate::syntax::syntax_to_source(syntax),
    }
}

fn reflect_ident(syntax: &Syntax) -> Option<String> {
    match &syntax.kind {
        SyntaxKind::Token(SyntaxToken::Ident(name)) => Some(name.clone()),
        _ => {
            let source = reflection_source(syntax);
            let tokens = Lexer::new(&source).tokenize().ok()?;
            let program = Parser::new(&tokens).parse_program().ok()?;
            program.stmts.iter().find_map(stmt_item_name)
        }
    }
}

fn reflect_type_of(syntax: &Syntax) -> Option<String> {
    let source = reflection_source(syntax);
    let tokens = Lexer::new(&source).tokenize().ok()?;
    if Parser::new(&tokens).parse_type_fragment().is_ok() {
        return Some(source);
    }
    let program = Parser::new(&tokens).parse_program().ok()?;
    program.stmts.iter().find_map(|stmt| match stmt {
        Stmt::Fn { ret_type, .. } => ret_type.as_ref().map(|ret| type_source(&ret.ty)),
        Stmt::Let { ty, .. } => ty.as_ref().map(type_source),
        Stmt::Type(type_def) => Some(type_def.name.clone()),
        Stmt::TypeAlias { ty, .. } => Some(type_source(ty)),
        Stmt::Extern { ty, .. } => Some(type_source(ty)),
        _ => None,
    })
}

fn reflect_fields(syntax: &Syntax) -> Vec<String> {
    let source = reflection_source(syntax);
    let Ok(tokens) = Lexer::new(&source).tokenize() else {
        return Vec::new();
    };
    let Ok(ty) = Parser::new(&tokens).parse_type_fragment() else {
        return Vec::new();
    };
    match ty {
        Type::Record(fields, _) => fields.into_iter().map(|(name, _)| name).collect(),
        _ => Vec::new(),
    }
}

fn reflect_program(
    span: SourceSpan,
    syntax: &Syntax,
) -> Result<crate::ast::Program, MacroRuntimeError> {
    let source = reflection_source(syntax);
    let tokens = Lexer::new(&source)
        .tokenize()
        .map_err(|_| MacroRuntimeError::new(span, "macro reflection expected valid Hern syntax"))?;
    Parser::new(&tokens)
        .parse_program()
        .map_err(|_| MacroRuntimeError::new(span, "macro reflection expected item syntax"))
}

fn stmt_item_name(stmt: &Stmt) -> Option<String> {
    match stmt {
        Stmt::Fn { name, .. }
        | Stmt::Op { name, .. }
        | Stmt::Macro(crate::ast::MacroDef { name, .. })
        | Stmt::Type(crate::ast::TypeDef { name, .. })
        | Stmt::TypeAlias { name, .. }
        | Stmt::Extern { name, .. } => Some(name.clone()),
        Stmt::Trait(trait_def) => Some(trait_def.name.clone()),
        Stmt::Impl(_)
        | Stmt::InherentImpl(_)
        | Stmt::TestBlock { .. }
        | Stmt::RecBlock { .. }
        | Stmt::Let { .. }
        | Stmt::Expr(_) => None,
    }
}

fn type_source(ty: &Type) -> String {
    match ty {
        Type::Ident(name) | Type::Var(name) => name.clone(),
        Type::App(con, args) => format!(
            "{}({})",
            type_source(con),
            args.iter().map(type_source).collect::<Vec<_>>().join(", ")
        ),
        Type::Func(params, ret) => format!(
            "fn({}) -> {}",
            params
                .iter()
                .map(|param| {
                    if param.mut_place {
                        format!("mut {}", type_source(&param.ty))
                    } else {
                        type_source(&param.ty)
                    }
                })
                .collect::<Vec<_>>()
                .join(", "),
            if ret.mut_place {
                format!("mut {}", type_source(&ret.ty))
            } else {
                type_source(&ret.ty)
            }
        ),
        Type::Tuple(items) => format!(
            "({})",
            items.iter().map(type_source).collect::<Vec<_>>().join(", ")
        ),
        Type::Record(fields, is_open) => {
            let mut parts = fields
                .iter()
                .map(|(name, ty)| format!("{name}: {}", type_source(ty)))
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

fn macro_value_to_syntax_delimiter(
    span: SourceSpan,
    value: MacroValue,
) -> Result<SyntaxDelimiter, MacroRuntimeError> {
    match value {
        MacroValue::Variant(name, None) if name == "Paren" => Ok(SyntaxDelimiter::Paren),
        MacroValue::Variant(name, None) if name == "Brace" => Ok(SyntaxDelimiter::Brace),
        MacroValue::Variant(name, None) if name == "Bracket" => Ok(SyntaxDelimiter::Bracket),
        _ => Err(MacroRuntimeError::new(
            span,
            "syntax_tree expects a SyntaxDelimiter",
        )),
    }
}

fn macro_value_to_syntax_vec(
    span: SourceSpan,
    value: MacroValue,
) -> Result<Vec<Syntax>, MacroRuntimeError> {
    match value {
        MacroValue::SyntaxArray(items) => Ok(items),
        MacroValue::Array(items) => items
            .into_iter()
            .map(|item| match item {
                MacroValue::Syntax(syntax) => Ok(syntax),
                _ => Err(MacroRuntimeError::new(
                    span,
                    "syntax children must be Syntax values",
                )),
            })
            .collect(),
        _ => Err(MacroRuntimeError::new(
            span,
            "syntax children must be an array of Syntax",
        )),
    }
}

fn macro_value_to_syntax_token(
    span: SourceSpan,
    name: &str,
    payload: Option<&MacroValue>,
) -> Result<SyntaxToken, MacroRuntimeError> {
    match (name, payload) {
        ("Ident", Some(MacroValue::Tuple(items))) => match items.as_slice() {
            [MacroValue::String(name), _] => Ok(SyntaxToken::Ident(name.clone())),
            _ => Err(MacroRuntimeError::new(span, "Ident token expects a name")),
        },
        ("Ident", Some(MacroValue::String(name))) => Ok(SyntaxToken::Ident(name.clone())),
        ("Keyword", Some(MacroValue::String(text))) => Ok(SyntaxToken::Keyword(text.clone())),
        ("Literal", Some(MacroValue::String(text))) => Ok(SyntaxToken::Literal(text.clone())),
        ("Operator", Some(MacroValue::String(text))) => Ok(SyntaxToken::Operator(text.clone())),
        ("Punct", Some(MacroValue::String(text))) => Ok(SyntaxToken::Punct(text.clone())),
        _ => Err(MacroRuntimeError::new(
            span,
            "syntax_token expects a SyntaxToken value",
        )),
    }
}

fn eval_macro_method_call(
    span: &SourceSpan,
    receiver: &CoreExpr,
    name: &str,
    args: &[CoreExpr],
    env: &mut MacroEnv,
    state: &mut MacroRuntimeState,
    helpers: &HashMap<String, Result<CoreFunction, MacroRuntimeError>>,
) -> Result<MacroValue, MacroRuntimeError> {
    let receiver = eval_expr(receiver, env, state, helpers)?;
    if matches!(receiver, MacroValue::Break(_)) {
        return Ok(receiver);
    }
    match (name, args.len()) {
        ("len", 0) => eval_len(*span, &receiver),
        ("is_empty", 0) => eval_len(*span, &receiver).map(|value| match value {
            MacroValue::Int(len) => MacroValue::Bool(len == 0),
            other => other,
        }),
        ("unwrap_or", 1) => match receiver {
            MacroValue::OptionSome(value) => Ok(*value),
            MacroValue::OptionNone => eval_expr(&args[0], env, state, helpers),
            _ => Err(MacroRuntimeError::new(
                *span,
                "unwrap_or expects an Option value",
            )),
        },
        _ => Err(MacroRuntimeError::new(
            *span,
            format!("unsupported macro-phase method `{name}`"),
        )),
    }
}

fn eval_len(span: SourceSpan, value: &MacroValue) -> Result<MacroValue, MacroRuntimeError> {
    match value {
        MacroValue::String(value) => Ok(MacroValue::Int(value.chars().count() as i32)),
        MacroValue::SyntaxArray(items) => Ok(MacroValue::Int(items.len() as i32)),
        MacroValue::Array(items) => Ok(MacroValue::Int(items.len() as i32)),
        MacroValue::Tuple(items) => Ok(MacroValue::Int(items.len() as i32)),
        _ => Err(MacroRuntimeError::new(
            span,
            "len expects an array or string",
        )),
    }
}

fn eval_field_access(
    span: SourceSpan,
    receiver: MacroValue,
    field: &str,
) -> Result<MacroValue, MacroRuntimeError> {
    match receiver {
        MacroValue::Record(fields) => fields
            .into_iter()
            .find_map(|(name, value)| (name == field).then_some(value))
            .ok_or_else(|| {
                MacroRuntimeError::new(span, format!("unknown macro-phase record field `{field}`"))
            }),
        _ => Err(MacroRuntimeError::new(
            span,
            "field access expects a record",
        )),
    }
}

fn eval_index(
    span: SourceSpan,
    receiver: MacroValue,
    key: MacroValue,
) -> Result<MacroValue, MacroRuntimeError> {
    let MacroValue::Int(index) = key else {
        return Err(MacroRuntimeError::new(span, "index key expects int"));
    };
    if index < 0 {
        return Err(MacroRuntimeError::new(span, "array index out of bounds"));
    }
    let index = index as usize;
    match receiver {
        MacroValue::SyntaxArray(items) => items
            .get(index)
            .cloned()
            .map(MacroValue::Syntax)
            .ok_or_else(|| MacroRuntimeError::new(span, "array index out of bounds")),
        MacroValue::Array(items) => items
            .get(index)
            .cloned()
            .ok_or_else(|| MacroRuntimeError::new(span, "array index out of bounds")),
        _ => Err(MacroRuntimeError::new(span, "index expects an array")),
    }
}

fn syntax_delimiter_value(delimiter: crate::syntax::SyntaxDelimiter) -> MacroValue {
    MacroValue::Variant(
        match delimiter {
            crate::syntax::SyntaxDelimiter::Paren => "Paren",
            crate::syntax::SyntaxDelimiter::Brace => "Brace",
            crate::syntax::SyntaxDelimiter::Bracket => "Bracket",
        }
        .to_string(),
        None,
    )
}

fn syntax_delimiter_ident_value(name: &str) -> Option<MacroValue> {
    matches!(name, "Paren" | "Brace" | "Bracket")
        .then(|| MacroValue::Variant(name.to_string(), None))
}

fn syntax_kind_value(syntax: &Syntax) -> MacroValue {
    let kind = match &syntax.kind {
        crate::syntax::SyntaxKind::Token(_) => "token",
        crate::syntax::SyntaxKind::Tree {
            delimiter: crate::syntax::SyntaxDelimiter::Paren,
            ..
        } => "tree:paren",
        crate::syntax::SyntaxKind::Tree {
            delimiter: crate::syntax::SyntaxDelimiter::Brace,
            ..
        } => "tree:brace",
        crate::syntax::SyntaxKind::Tree {
            delimiter: crate::syntax::SyntaxDelimiter::Bracket,
            ..
        } => "tree:bracket",
        crate::syntax::SyntaxKind::Sequence(_) => "sequence",
    };
    MacroValue::String(kind.to_string())
}

fn syntax_span_value(span: SourceSpan) -> MacroValue {
    MacroValue::Tuple(vec![
        MacroValue::Int(span.start_line as i32),
        MacroValue::Int(span.start_col as i32),
        MacroValue::Int(span.end_line as i32),
        MacroValue::Int(span.end_col as i32),
    ])
}

fn syntax_origin_value(origin: &crate::syntax::SyntaxOrigin) -> MacroValue {
    let origin = match origin {
        crate::syntax::SyntaxOrigin::Source(_) => "source",
        crate::syntax::SyntaxOrigin::Generated => "generated",
    };
    MacroValue::String(origin.to_string())
}

fn eval_intrinsic_call(
    span: SourceSpan,
    intrinsic: CoreIntrinsic,
    args: &[CoreExpr],
    env: &mut MacroEnv,
    state: &mut MacroRuntimeState,
    helpers: &HashMap<String, Result<CoreFunction, MacroRuntimeError>>,
) -> Result<MacroValue, MacroRuntimeError> {
    match intrinsic {
        CoreIntrinsic::Not => {
            expect_intrinsic_arity(span, "!", args, 1)?;
            match eval_expr(&args[0], env, state, helpers)? {
                value @ MacroValue::Break(_) => Ok(value),
                MacroValue::Bool(value) => Ok(MacroValue::Bool(!value)),
                _ => Err(MacroRuntimeError::new(
                    args[0].span,
                    "! expects bool operand",
                )),
            }
        }
        CoreIntrinsic::Neg => {
            expect_intrinsic_arity(span, "-", args, 1)?;
            match eval_expr(&args[0], env, state, helpers)? {
                value @ MacroValue::Break(_) => Ok(value),
                MacroValue::Int(value) => Ok(MacroValue::Int(-value)),
                _ => Err(MacroRuntimeError::new(
                    args[0].span,
                    "- expects int operand",
                )),
            }
        }
        CoreIntrinsic::And => {
            expect_intrinsic_arity(span, "&&", args, 2)?;
            let lhs = &args[0];
            let rhs = &args[1];
            match eval_expr(lhs, env, state, helpers)? {
                value @ MacroValue::Break(_) => Ok(value),
                MacroValue::Bool(false) => Ok(MacroValue::Bool(false)),
                MacroValue::Bool(true) => match eval_expr(rhs, env, state, helpers)? {
                    value @ MacroValue::Break(_) => Ok(value),
                    MacroValue::Bool(value) => Ok(MacroValue::Bool(value)),
                    _ => Err(MacroRuntimeError::new(rhs.span, "&& expects bool operands")),
                },
                _ => Err(MacroRuntimeError::new(lhs.span, "&& expects bool operands")),
            }
        }
        CoreIntrinsic::Or => {
            expect_intrinsic_arity(span, "||", args, 2)?;
            let lhs = &args[0];
            let rhs = &args[1];
            match eval_expr(lhs, env, state, helpers)? {
                value @ MacroValue::Break(_) => Ok(value),
                MacroValue::Bool(true) => Ok(MacroValue::Bool(true)),
                MacroValue::Bool(false) => match eval_expr(rhs, env, state, helpers)? {
                    value @ MacroValue::Break(_) => Ok(value),
                    MacroValue::Bool(value) => Ok(MacroValue::Bool(value)),
                    _ => Err(MacroRuntimeError::new(rhs.span, "|| expects bool operands")),
                },
                _ => Err(MacroRuntimeError::new(lhs.span, "|| expects bool operands")),
            }
        }
        CoreIntrinsic::Eq | CoreIntrinsic::NotEq => {
            expect_intrinsic_arity(span, equality_intrinsic_name(intrinsic), args, 2)?;
            let lhs_expr = &args[0];
            let rhs_expr = &args[1];
            let lhs = eval_expr(lhs_expr, env, state, helpers)?;
            if matches!(lhs, MacroValue::Break(_)) {
                return Ok(lhs);
            }
            let rhs = eval_expr(rhs_expr, env, state, helpers)?;
            if matches!(rhs, MacroValue::Break(_)) {
                return Ok(rhs);
            }
            let result = macro_value_eq(&lhs, &rhs)
                .ok_or_else(|| MacroRuntimeError::new(span, "unsupported macro-phase equality"))?;
            Ok(MacroValue::Bool(match intrinsic {
                CoreIntrinsic::Eq => result,
                CoreIntrinsic::NotEq => !result,
                CoreIntrinsic::Not
                | CoreIntrinsic::Neg
                | CoreIntrinsic::And
                | CoreIntrinsic::Or
                | CoreIntrinsic::Add
                | CoreIntrinsic::Sub
                | CoreIntrinsic::Lt
                | CoreIntrinsic::Le
                | CoreIntrinsic::Gt
                | CoreIntrinsic::Ge => unreachable!(),
            }))
        }
        CoreIntrinsic::Add
        | CoreIntrinsic::Sub
        | CoreIntrinsic::Lt
        | CoreIntrinsic::Le
        | CoreIntrinsic::Gt
        | CoreIntrinsic::Ge => {
            expect_intrinsic_arity(span, int_intrinsic_name(intrinsic), args, 2)?;
            let lhs = eval_expr(&args[0], env, state, helpers)?;
            if matches!(lhs, MacroValue::Break(_)) {
                return Ok(lhs);
            }
            let rhs = eval_expr(&args[1], env, state, helpers)?;
            if matches!(rhs, MacroValue::Break(_)) {
                return Ok(rhs);
            }
            let (MacroValue::Int(lhs), MacroValue::Int(rhs)) = (lhs, rhs) else {
                return Err(MacroRuntimeError::new(
                    span,
                    "integer operator expects int operands",
                ));
            };
            Ok(match intrinsic {
                CoreIntrinsic::Add => MacroValue::Int(lhs + rhs),
                CoreIntrinsic::Sub => MacroValue::Int(lhs - rhs),
                CoreIntrinsic::Lt => MacroValue::Bool(lhs < rhs),
                CoreIntrinsic::Le => MacroValue::Bool(lhs <= rhs),
                CoreIntrinsic::Gt => MacroValue::Bool(lhs > rhs),
                CoreIntrinsic::Ge => MacroValue::Bool(lhs >= rhs),
                CoreIntrinsic::Not
                | CoreIntrinsic::Neg
                | CoreIntrinsic::Eq
                | CoreIntrinsic::NotEq
                | CoreIntrinsic::And
                | CoreIntrinsic::Or => unreachable!(),
            })
        }
    }
}

fn expect_intrinsic_arity(
    span: SourceSpan,
    name: &str,
    args: &[CoreExpr],
    expected: usize,
) -> Result<(), MacroRuntimeError> {
    if args.len() == expected {
        Ok(())
    } else {
        Err(MacroRuntimeError::new(
            span,
            format!(
                "wrong number of macro-phase `{name}` arguments: expected {expected}, got {}",
                args.len()
            ),
        ))
    }
}

fn equality_intrinsic_name(intrinsic: CoreIntrinsic) -> &'static str {
    match intrinsic {
        CoreIntrinsic::Eq => "==",
        CoreIntrinsic::NotEq => "!=",
        _ => unreachable!(),
    }
}

fn int_intrinsic_name(intrinsic: CoreIntrinsic) -> &'static str {
    match intrinsic {
        CoreIntrinsic::Add => "+",
        CoreIntrinsic::Sub => "-",
        CoreIntrinsic::Lt => "<",
        CoreIntrinsic::Le => "<=",
        CoreIntrinsic::Gt => ">",
        CoreIntrinsic::Ge => ">=",
        _ => unreachable!(),
    }
}

fn eval_helper_call(
    span: SourceSpan,
    name: &str,
    args: &[CoreExpr],
    env: &mut MacroEnv,
    state: &mut MacroRuntimeState,
    helpers: &HashMap<String, Result<CoreFunction, MacroRuntimeError>>,
) -> Result<MacroValue, MacroRuntimeError> {
    let function = helpers
        .get(name)
        .expect("helper existence checked before eval_helper_call")
        .clone()?;
    eval_function_call(span, &function, args, env, MacroEnv::new(), state, helpers)
}

fn eval_function_call(
    span: SourceSpan,
    function: &CoreFunction,
    args: &[CoreExpr],
    caller_env: &mut MacroEnv,
    mut callee_env: MacroEnv,
    state: &mut MacroRuntimeState,
    helpers: &HashMap<String, Result<CoreFunction, MacroRuntimeError>>,
) -> Result<MacroValue, MacroRuntimeError> {
    if args.len() != function.params.len() {
        return Err(MacroRuntimeError::new(
            span,
            format!(
                "wrong number of macro-phase function arguments: expected {}, got {}",
                function.params.len(),
                args.len()
            ),
        ));
    }
    state.enter_call(span)?;
    let result = (|| {
        let mut values = Vec::with_capacity(args.len());
        for arg in args {
            let value = eval_expr(arg, caller_env, state, helpers)?;
            if matches!(value, MacroValue::Break(_)) {
                return Ok(value);
            }
            values.push(value);
        }
        for (pattern, value) in function.params.iter().zip(values) {
            bind_runtime_pattern(pattern, value, &mut callee_env)?;
        }
        eval_expr(&function.body, &mut callee_env, state, helpers)
    })();
    state.exit_call();
    result
}

fn bind_runtime_pattern(
    pattern: &Pattern,
    value: MacroValue,
    env: &mut MacroEnv,
) -> Result<(), MacroRuntimeError> {
    let mut scoped = env.clone();
    if match_macro_pattern(pattern, &value, &mut scoped)? {
        *env = scoped;
        Ok(())
    } else {
        Err(MacroRuntimeError::new(
            pattern_span(pattern),
            "macro-phase pattern did not match",
        ))
    }
}
