use crate::ast::{Pattern, SourceSpan};
use crate::syntax::Syntax;
use std::collections::{HashMap, HashSet};

use super::core_ir::{
    CoreAssignTarget, CoreBinaryOp, CoreCallee, CoreExpr, CoreExprKind, CoreFunction, CoreStmt,
    CoreStmtKind,
};
use super::diagnostics::{MacroRuntimeError, pattern_span};
use super::pattern::match_macro_pattern;
use super::runtime::MacroRuntimeState;
use super::source::syntax_token_source;
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
    env.insert(param_name.to_string(), MacroValue::Syntax(input));
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
        CoreExprKind::Ident(name) => env.get(name).cloned().ok_or_else(|| {
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
            Err(MacroRuntimeError::new(
                expr.span,
                "non-exhaustive macro match",
            ))
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
        CoreExprKind::Binary { lhs, op, rhs } => {
            eval_binary(expr.span, lhs, *op, rhs, env, state, helpers)
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
    if let Pattern::Variable(name, _) = pattern {
        local_bindings.insert(name.clone());
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

fn eval_binary(
    span: SourceSpan,
    lhs: &CoreExpr,
    op: CoreBinaryOp,
    rhs: &CoreExpr,
    env: &mut MacroEnv,
    state: &mut MacroRuntimeState,
    helpers: &HashMap<String, Result<CoreFunction, MacroRuntimeError>>,
) -> Result<MacroValue, MacroRuntimeError> {
    match op {
        CoreBinaryOp::And => match eval_expr(lhs, env, state, helpers)? {
            value @ MacroValue::Break(_) => Ok(value),
            MacroValue::Bool(false) => Ok(MacroValue::Bool(false)),
            MacroValue::Bool(true) => match eval_expr(rhs, env, state, helpers)? {
                value @ MacroValue::Break(_) => Ok(value),
                MacroValue::Bool(value) => Ok(MacroValue::Bool(value)),
                _ => Err(MacroRuntimeError::new(rhs.span, "&& expects bool operands")),
            },
            _ => Err(MacroRuntimeError::new(lhs.span, "&& expects bool operands")),
        },
        CoreBinaryOp::Or => match eval_expr(lhs, env, state, helpers)? {
            value @ MacroValue::Break(_) => Ok(value),
            MacroValue::Bool(true) => Ok(MacroValue::Bool(true)),
            MacroValue::Bool(false) => match eval_expr(rhs, env, state, helpers)? {
                value @ MacroValue::Break(_) => Ok(value),
                MacroValue::Bool(value) => Ok(MacroValue::Bool(value)),
                _ => Err(MacroRuntimeError::new(rhs.span, "|| expects bool operands")),
            },
            _ => Err(MacroRuntimeError::new(lhs.span, "|| expects bool operands")),
        },
        CoreBinaryOp::Eq | CoreBinaryOp::NotEq => {
            let lhs = eval_expr(lhs, env, state, helpers)?;
            if matches!(lhs, MacroValue::Break(_)) {
                return Ok(lhs);
            }
            let rhs = eval_expr(rhs, env, state, helpers)?;
            if matches!(rhs, MacroValue::Break(_)) {
                return Ok(rhs);
            }
            let result = macro_value_eq(&lhs, &rhs)
                .ok_or_else(|| MacroRuntimeError::new(span, "unsupported macro-phase equality"))?;
            Ok(MacroValue::Bool(match op {
                CoreBinaryOp::Eq => result,
                CoreBinaryOp::NotEq => !result,
                CoreBinaryOp::And
                | CoreBinaryOp::Or
                | CoreBinaryOp::Add
                | CoreBinaryOp::Sub
                | CoreBinaryOp::Lt
                | CoreBinaryOp::Le
                | CoreBinaryOp::Gt
                | CoreBinaryOp::Ge => unreachable!(),
            }))
        }
        CoreBinaryOp::Add
        | CoreBinaryOp::Sub
        | CoreBinaryOp::Lt
        | CoreBinaryOp::Le
        | CoreBinaryOp::Gt
        | CoreBinaryOp::Ge => {
            let lhs = eval_expr(lhs, env, state, helpers)?;
            if matches!(lhs, MacroValue::Break(_)) {
                return Ok(lhs);
            }
            let rhs = eval_expr(rhs, env, state, helpers)?;
            if matches!(rhs, MacroValue::Break(_)) {
                return Ok(rhs);
            }
            let (MacroValue::Int(lhs), MacroValue::Int(rhs)) = (lhs, rhs) else {
                return Err(MacroRuntimeError::new(
                    span,
                    "integer operator expects int operands",
                ));
            };
            Ok(match op {
                CoreBinaryOp::Add => MacroValue::Int(lhs + rhs),
                CoreBinaryOp::Sub => MacroValue::Int(lhs - rhs),
                CoreBinaryOp::Lt => MacroValue::Bool(lhs < rhs),
                CoreBinaryOp::Le => MacroValue::Bool(lhs <= rhs),
                CoreBinaryOp::Gt => MacroValue::Bool(lhs > rhs),
                CoreBinaryOp::Ge => MacroValue::Bool(lhs >= rhs),
                CoreBinaryOp::Eq | CoreBinaryOp::NotEq | CoreBinaryOp::And | CoreBinaryOp::Or => {
                    unreachable!()
                }
            })
        }
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
    match pattern {
        Pattern::Wildcard => Ok(()),
        Pattern::Variable(name, _) => {
            env.insert(name.clone(), value);
            Ok(())
        }
        _ => Err(MacroRuntimeError::new(
            pattern_span(pattern),
            "unsupported let pattern in macro body",
        )),
    }
}
