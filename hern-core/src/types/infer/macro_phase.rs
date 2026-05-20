//! Macro definition inference.
//!
//! Macro bodies are phase-1 Hern: they are checked at authoring time, produce
//! normal editor metadata, and must return `MacroResult(Syntax)`. The current
//! macro executor still supports a restricted expression subset, but typing
//! lives here so the compiler and LSP have one explicit phase-1 entry point.

use super::*;

impl Infer {
    pub(super) fn infer_macro_defs(
        &mut self,
        env: &TypeEnv,
        defs: &mut [MacroDef],
    ) -> Result<(), SpannedTypeError> {
        for def in defs {
            self.infer_macro_def(env, def)?;
        }
        Ok(())
    }

    fn infer_macro_def(
        &mut self,
        env: &TypeEnv,
        def: &mut MacroDef,
    ) -> Result<(), SpannedTypeError> {
        let syntax_ty = Ty::Con("Syntax".to_string());
        let mut param_vars = HashMap::new();
        let param_ty = self
            .ast_to_ty_with_vars(&def.param_ty, &mut param_vars)
            .map_err(|err| err.at(def.param_ty_span))?;
        if param_ty != syntax_ty {
            return Err(TypeError::InvalidMacroSignature {
                message: format!("input parameter must have type `Syntax`, got `{param_ty}`"),
            }
            .at(def.param_ty_span));
        }

        let ret_ty = self
            .ast_to_ty_with_vars(&def.ret_ty, &mut param_vars)
            .map_err(|err| err.at(def.ret_ty_span))?;
        let expected_ret_ty = macro_result_syntax_ty();
        if ret_ty != expected_ret_ty {
            return Err(TypeError::InvalidMacroSignature {
                message: format!("return type must be `MacroResult(Syntax)`, got `{ret_ty}`"),
            }
            .at(def.ret_ty_span));
        }

        if !matches!(def.body.kind, ExprKind::Block { .. }) {
            return Err(TypeError::InvalidMacroSignature {
                message: "body must be a block expression".to_string(),
            }
            .at(def.body.span));
        }

        let mut macro_env = macro_phase_env(env);
        self.metadata
            .record_binding_type(def.param_span, syntax_ty.clone());
        macro_env.insert(
            def.param_name.clone(),
            EnvInfo::immutable(Scheme::mono(syntax_ty.clone())),
        );

        let body_ty = self.infer_expr(&macro_env, &mut def.body)?;
        unify(&mut self.subst, body_ty, macro_result_syntax_ty())
            .map_err(|err| err.at(def.body.span))
    }
}

fn macro_result_syntax_ty() -> Ty {
    Ty::App(
        Box::new(Ty::Con("Result".to_string())),
        vec![
            Ty::Con("Syntax".to_string()),
            Ty::Con("MacroError".to_string()),
        ],
    )
}

fn macro_phase_env(env: &TypeEnv) -> TypeEnv {
    let mut phase_env = TypeEnv::new();
    for (name, info) in env.iter() {
        if info.macro_phase_available || macro_builtin_available(name) {
            phase_env.insert(name.clone(), info.clone());
        }
    }
    phase_env
}

fn macro_builtin_available(name: &str) -> bool {
    matches!(
        name,
        "Ok" | "Err"
            | "MacroError"
            | "syntax_children"
            | "syntax_token_text"
            | "syntax_is_ident"
            | "to_string"
    )
}
