use crate::analysis::CompilerDiagnostic;
use crate::ast::{Expr, ExprKind, Program, SourceSpan, Stmt};
use crate::lex::Lexer;
use crate::parse::Parser;
use crate::syntax::Syntax;

use super::registry::{MacroRegistry, collect_macros};
use super::runtime::{MacroRuntime, MacroRuntimeLimits};
use super::source::syntax_source;

const DEFAULT_MAX_EXPANSIONS: usize = 256;
const DEFAULT_MAX_EVAL_STEPS: usize = 20_000;
const DEFAULT_MAX_OUTPUT_SYNTAX_NODES: usize = 10_000;
const DEFAULT_MAX_CALL_DEPTH: usize = 64;
const DEFAULT_MAX_GENERATED_SOURCE_BYTES: usize = 1_000_000;

pub fn expand_macros(program: &mut Program) -> Result<(), CompilerDiagnostic> {
    expand_macros_with_options(program, MacroExecutionOptions::default())
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
    let helpers = registry.helpers();
    let mut ctx = ExpansionCtx {
        registry,
        runtime: MacroRuntime::new(options.runtime_limits(), helpers),
        options,
    };
    expand_top_level_stmts(&mut program.stmts, &mut ctx)
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
    runtime: MacroRuntime,
    options: MacroExecutionOptions,
}

fn expand_top_level_stmts(
    stmts: &mut [Stmt],
    ctx: &mut ExpansionCtx,
) -> Result<(), CompilerDiagnostic> {
    for stmt in stmts {
        if matches!(stmt, Stmt::Macro(_)) {
            continue;
        }
        expand_stmt(stmt, ctx)?;
    }
    Ok(())
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

fn expand_expr(expr: &mut Expr, ctx: &mut ExpansionCtx) -> Result<(), CompilerDiagnostic> {
    match &mut expr.kind {
        ExprKind::MacroCall {
            name,
            name_span,
            input,
            ..
        } => {
            if ctx.options.max_expansions == 0 {
                return Err(CompilerDiagnostic::error(
                    Some(*name_span),
                    "macro expansion fuel exhausted",
                ));
            }
            ctx.options.max_expansions -= 1;
            let def = ctx.registry.get(name).cloned().ok_or_else(|| {
                CompilerDiagnostic::error(Some(*name_span), format!("unknown macro `{name}!`"))
            })?;
            let expanded = ctx
                .runtime
                .run_macro(&def, input.clone(), expr.span)
                .map_err(|err| {
                    CompilerDiagnostic::error(
                        Some(err.span),
                        format!("macro `{name}!`: {}", err.message),
                    )
                })?;
            *expr =
                parse_expanded_expr(&expanded, expr.span, ctx.options.max_generated_source_bytes)?;
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

fn parse_expanded_expr(
    syntax: &Syntax,
    call_span: SourceSpan,
    generated_source_bytes: usize,
) -> Result<Expr, CompilerDiagnostic> {
    let source = syntax_source(syntax);
    if source.len() > generated_source_bytes {
        return Err(CompilerDiagnostic::error(
            Some(call_span),
            format!(
                "macro generated too much source: {} bytes exceeds limit {generated_source_bytes}",
                source.len()
            ),
        ));
    }
    let tokens = Lexer::new(&source).tokenize().map_err(|err| {
        CompilerDiagnostic::error(
            Some(call_span),
            format!("macro expansion produced invalid tokens: {:?}", err.kind),
        )
    })?;
    Parser::new(&tokens).parse_expr_fragment().map_err(|err| {
        CompilerDiagnostic::error(
            Some(call_span),
            format!(
                "macro expansion did not produce an expression: {}",
                err.message
            ),
        )
    })
}
