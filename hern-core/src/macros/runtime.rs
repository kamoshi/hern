use crate::ast::{MacroDef, SourceSpan};
use crate::syntax::Syntax;
use std::collections::HashMap;

use super::core_ir::{CoreFunction, lower_macro_body_to_core, lower_macro_function_to_core};
use super::diagnostics::MacroRuntimeError;
use super::eval::eval_macro_result;
use super::registry::MacroHelperDef;
use super::source::syntax_node_count;

#[derive(Debug, Clone, Copy)]
pub(super) struct MacroRuntimeLimits {
    pub(super) eval_steps: usize,
    pub(super) output_syntax_nodes: usize,
    pub(super) call_depth: usize,
}

pub(super) struct MacroRuntime {
    limits: MacroRuntimeLimits,
    helpers: HashMap<String, Result<CoreFunction, MacroRuntimeError>>,
}

impl MacroRuntime {
    pub(super) fn new(
        limits: MacroRuntimeLimits,
        helpers: HashMap<String, MacroHelperDef>,
    ) -> Self {
        let helpers = helpers
            .into_iter()
            .map(|(name, helper)| {
                let lowered =
                    lower_macro_function_to_core(&helper.params, &helper.body).map_err(|err| {
                        MacroRuntimeError::new(
                            err.span,
                            format!(
                                "cannot use `{}` as a macro-phase helper: {}",
                                helper.name, err.message
                            ),
                        )
                    });
                (name, lowered)
            })
            .collect();
        Self { limits, helpers }
    }

    pub(super) fn run_macro(
        &self,
        def: &MacroDef,
        input: Syntax,
        call_span: SourceSpan,
    ) -> Result<Syntax, MacroRuntimeError> {
        let body = lower_macro_body_to_core(&def.body)?;
        let mut state = MacroRuntimeState::new(self.limits, call_span);
        let syntax = eval_macro_result(
            &body.expr,
            &def.param_name,
            input,
            call_span,
            &mut state,
            &self.helpers,
        )?;
        let node_count = syntax_node_count(&syntax);
        if node_count > self.limits.output_syntax_nodes {
            return Err(MacroRuntimeError::new(
                call_span,
                format!(
                    "macro generated too much syntax: {node_count} nodes exceeds limit {}",
                    self.limits.output_syntax_nodes
                ),
            ));
        }
        Ok(syntax)
    }
}

pub(super) struct MacroRuntimeState {
    remaining_steps: usize,
    remaining_call_depth: usize,
    macro_call_span: SourceSpan,
    next_fresh_scope: u32,
}

impl MacroRuntimeState {
    fn new(limits: MacroRuntimeLimits, macro_call_span: SourceSpan) -> Self {
        Self {
            remaining_steps: limits.eval_steps,
            remaining_call_depth: limits.call_depth,
            macro_call_span,
            next_fresh_scope: 100_000,
        }
    }

    pub(super) fn spend(&mut self, span: SourceSpan) -> Result<(), MacroRuntimeError> {
        let Some(remaining) = self.remaining_steps.checked_sub(1) else {
            return Err(MacroRuntimeError::new(
                span,
                "macro comptime step limit exceeded",
            ));
        };
        self.remaining_steps = remaining;
        Ok(())
    }

    pub(super) fn enter_call(&mut self, span: SourceSpan) -> Result<(), MacroRuntimeError> {
        let Some(remaining) = self.remaining_call_depth.checked_sub(1) else {
            return Err(MacroRuntimeError::new(
                span,
                "macro comptime call depth limit exceeded",
            ));
        };
        self.remaining_call_depth = remaining;
        Ok(())
    }

    pub(super) fn exit_call(&mut self) {
        self.remaining_call_depth += 1;
    }

    pub(super) fn macro_call_span(&self) -> SourceSpan {
        self.macro_call_span
    }

    pub(super) fn fresh_scope_id(&mut self) -> u32 {
        let id = self.next_fresh_scope;
        self.next_fresh_scope = self.next_fresh_scope.saturating_add(1);
        id
    }
}
