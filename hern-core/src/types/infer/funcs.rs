//! Function and closure inference.
//!
//! Function-like expressions introduce parameter bindings, return expectations,
//! and capability metadata. Named declaration generalization lives in the
//! declaration and scheme modules.

use super::*;

impl Infer {
    pub(super) fn check_fresh_return_expr(
        &self,
        expr: &Expr,
        ret: &FuncReturn,
    ) -> Result<(), SpannedTypeError> {
        if ret.capability == ReturnCapability::FreshPlace && !self.is_fresh_mutable_place_expr(expr)
        {
            return Err(TypeError::ExpectedMutablePlace {
                subject: MutablePlaceSubject::ReturnValue,
                reason: MutablePlaceErrorReason::NotFresh,
            }
            .at(expr.span));
        }
        Ok(())
    }

    // ── Shared Fn/Op inference helper ─────────────────────────────────────────

    /// Infers a function or operator definition, inserting the resulting scheme
    /// into `env`. `add_self_binding` enables recursive calls (set for `fn`,
    /// not for `op`).
    #[allow(clippy::too_many_arguments)]
    pub(super) fn infer_fn_like(
        &mut self,
        env: &mut TypeEnv,
        name: &str,
        name_span: SourceSpan,
        params: &[Param],
        ret_type: &Option<TypeReturn>,
        body: &mut Expr,
        dict_params: &mut Vec<String>,
        type_bounds: &[TypeBound],
        add_self_binding: bool,
        macro_phase_available: bool,
    ) -> Result<(), SpannedTypeError> {
        let ambient = self.current_level;
        let (fn_ty, fn_constraints) = self.with_child_level(|this| {
            let mut param_vars: HashMap<String, TyVar> = HashMap::new();
            let mut param_tys = Vec::new();
            let mut body_env = env.clone();
            let initial_constraints =
                this.collect_type_bound_constraints(&mut param_vars, type_bounds)?;

            for param in params {
                if !is_irrefutable_param(&param.pat, &this.types.variant_env) {
                    return Err(TypeError::RefutableParamPattern.at(body.span));
                }
                let p_ty = match &param.ty {
                    Some(t) => this.ast_to_ty_with_vars(t, &mut param_vars)?,
                    None => this.fresh_ty(),
                };
                param_tys.push(p_ty.clone());
                this.check_param_pattern(&param.pat, p_ty, &mut body_env, param.mut_place)?;
            }

            let ret_ty = match ret_type {
                Some(t) => this.ast_to_ty_with_vars(&t.ty, &mut param_vars)?,
                None => this.fresh_ty(),
            };

            let fn_ret = func_return_from_annotation(ret_type, ret_ty.clone());
            let fn_ty = Ty::Func(func_params_from_params(params, param_tys), fn_ret.clone());

            if add_self_binding {
                body_env.insert(
                    name.to_string(),
                    EnvInfo::immutable(Scheme::mono(fn_ty.clone())),
                );
            }

            let (_, fn_constraints) =
                this.with_pending_constraints_scope(initial_constraints, |this| {
                    let body_ty = this.with_fn_return_scope(fn_ret.clone(), |this| {
                        if ret_type.is_some() {
                            this.infer_expr_expected(&body_env, body, ret_ty.clone())
                        } else {
                            this.infer_expr(&body_env, body)
                        }
                    })?;
                    unify_expr_result(&mut this.subst, body_ty.clone(), ret_ty)
                        .map_err(|err| err.at(body.span))?;
                    if !matches!(this.subst.apply(&body_ty), Ty::Never) {
                        this.check_fresh_return_expr(body, &fn_ret)?;
                    }
                    Ok(())
                })?;
            Ok((fn_ty, fn_constraints))
        })?;
        let finalized = self.finalize_constraints_at(env, fn_ty, fn_constraints, ambient);
        self.constraints.pending.extend(finalized.bubbled.clone());

        *dict_params = finalized.owned.iter().map(dict_param_name).collect();

        if add_self_binding && !finalized.owned.is_empty() {
            attach_owned_dicts_to_recursive_self_calls(body, name, &finalized.owned);
        }

        let resolver = |p: &PendingDictArg| {
            resolve_local_or_concrete(
                p,
                &finalized.owned,
                env,
                &self.impls.active_dicts,
                &self.impls.known_schemes,
                &self.subst,
            )
        };
        resolve_dict_uses_expr(body, &resolver, false)?;

        env.insert(
            name.to_string(),
            if macro_phase_available {
                EnvInfo::immutable(finalized.scheme.clone()).with_macro_phase_available()
            } else {
                EnvInfo::immutable(finalized.scheme.clone())
            },
        );
        self.metadata
            .record_definition_scheme(name_span, finalized.scheme);
        Ok(())
    }

    pub(super) fn infer_let_value_ty(
        &mut self,
        env: &TypeEnv,
        ty: &Option<Type>,
        value: &mut Expr,
    ) -> Result<Ty, SpannedTypeError> {
        if let Some(ast_ty) = ty {
            let mut param_vars = HashMap::new();
            let expected_ty = self.ast_to_ty_with_vars(ast_ty, &mut param_vars)?;
            let value_ty = self.infer_expr_expected(env, value, expected_ty.clone())?;
            unify_expr_result(&mut self.subst, value_ty, expected_ty.clone())
                .map_err(|err| err.at(value.span))?;
            Ok(expected_ty)
        } else {
            self.infer_expr(env, value)
        }
    }

    #[allow(clippy::too_many_arguments)]
    pub(super) fn infer_lambda_expr(
        &mut self,
        env: &TypeEnv,
        expr_id: NodeId,
        params: &[Param],
        annotated_return: Option<&Type>,
        body: &mut Expr,
        dict_params: &mut Vec<String>,
        expected_func: Option<(Vec<FuncParam>, FuncReturn)>,
    ) -> Result<Ty, SpannedTypeError> {
        let ambient = self.current_level;
        let (fn_ty, fn_constraints) = self.with_child_level(|this| {
            let mut param_vars: HashMap<String, TyVar> = HashMap::new();
            let mut param_tys = Vec::new();
            let mut body_env = env.clone();

            if let Some((expected_params, _)) = &expected_func
                && expected_params.len() != params.len()
            {
                return Err(TypeError::ArityMismatch {
                    expected: expected_params.len(),
                    got: params.len(),
                }
                .at(body.span));
            }

            for (idx, param) in params.iter().enumerate() {
                if !is_irrefutable_param(&param.pat, &this.types.variant_env) {
                    return Err(TypeError::RefutableParamPattern.at(body.span));
                }
                let expected_param = expected_func
                    .as_ref()
                    .and_then(|(expected_params, _)| expected_params.get(idx));
                if let Some(expected_param) = expected_param
                    && expected_param.capability.is_mut_place() != param.mut_place
                {
                    return Err(TypeError::MutableFunctionCapabilityMismatch.at(body.span));
                }
                let p_ty = match (&param.ty, expected_param) {
                    (Some(t), Some(expected_param)) => {
                        let annotated = this.ast_to_ty_with_vars(t, &mut param_vars)?;
                        unify(
                            &mut this.subst,
                            annotated.clone(),
                            expected_param.ty.clone(),
                        )
                        .map_err(|err| err.at(body.span))?;
                        annotated
                    }
                    (Some(t), None) => this.ast_to_ty_with_vars(t, &mut param_vars)?,
                    (None, Some(expected_param)) => expected_param.ty.clone(),
                    (None, None) => this.fresh_ty(),
                };
                param_tys.push(p_ty.clone());
                this.check_param_pattern(&param.pat, p_ty, &mut body_env, param.mut_place)?;
            }

            let (ret_ty, ret_capability) = match (&expected_func, annotated_return) {
                (Some((_, expected_ret)), Some(annotated)) => {
                    let annotated_ty = this.ast_to_ty_with_vars(annotated, &mut param_vars)?;
                    unify(
                        &mut this.subst,
                        annotated_ty.clone(),
                        (*expected_ret.ty).clone(),
                    )
                    .map_err(|err| err.at(body.span))?;
                    (annotated_ty, expected_ret.capability)
                }
                (Some((_, expected_ret)), None) => {
                    ((*expected_ret.ty).clone(), expected_ret.capability)
                }
                (None, Some(annotated)) => (
                    this.ast_to_ty_with_vars(annotated, &mut param_vars)?,
                    ReturnCapability::Value,
                ),
                (None, None) => (this.fresh_ty(), ReturnCapability::Value),
            };
            let fn_ret = FuncReturn {
                ty: Box::new(ret_ty.clone()),
                capability: ret_capability,
            };
            let (_, fn_constraints) = this.with_pending_constraints_scope(Vec::new(), |this| {
                let body_ty = this.with_fn_return_scope(fn_ret.clone(), |this| {
                    if expected_func.is_some() {
                        this.infer_expr_expected(&body_env, body, ret_ty.clone())
                    } else {
                        this.infer_expr(&body_env, body)
                    }
                })?;
                unify_expr_result(&mut this.subst, body_ty.clone(), ret_ty.clone())?;
                if !matches!(this.subst.apply(&body_ty), Ty::Never) {
                    this.check_fresh_return_expr(body, &fn_ret)?;
                }
                Ok(())
            })?;

            let fn_ty = Ty::Func(
                func_params_from_params(params, param_tys),
                FuncReturn {
                    ty: Box::new(this.subst.apply(&ret_ty)),
                    capability: ret_capability,
                },
            );
            Ok((fn_ty, fn_constraints))
        })?;
        let finalized = self.finalize_constraints_at(env, fn_ty, fn_constraints, ambient);
        self.constraints.pending.extend(finalized.bubbled.clone());
        *dict_params = finalized.owned.iter().map(dict_param_name).collect();

        let resolver = |p: &PendingDictArg| {
            resolve_local_or_concrete(
                p,
                &finalized.owned,
                env,
                &self.impls.active_dicts,
                &self.impls.known_schemes,
                &self.subst,
            )
        };
        resolve_dict_uses_expr_lenient(body, &resolver, false)?;

        self.record_callable_capabilities(expr_id, param_capabilities(params));

        Ok(if finalized.owned.is_empty() {
            finalized.scheme.ty
        } else {
            Ty::Qualified(finalized.owned, Box::new(finalized.scheme.ty))
        })
    }
}

pub(super) fn param_capabilities(params: &[Param]) -> Vec<ParamCapability> {
    params
        .iter()
        .map(|param| {
            if param.mut_place {
                ParamCapability::MutPlace
            } else {
                ParamCapability::Value
            }
        })
        .collect()
}

pub(super) fn func_params_from_params(params: &[Param], param_tys: Vec<Ty>) -> Vec<FuncParam> {
    params
        .iter()
        .zip(param_tys)
        .map(|(param, ty)| {
            if param.mut_place {
                FuncParam::mut_place(ty)
            } else {
                FuncParam::value(ty)
            }
        })
        .collect()
}

pub(super) fn func_return_from_annotation(ret_type: &Option<TypeReturn>, ret_ty: Ty) -> FuncReturn {
    if ret_type.as_ref().is_some_and(|ret| ret.mut_place) {
        FuncReturn::fresh_place(ret_ty)
    } else {
        value_func_return(ret_ty)
    }
}

pub(super) fn unify_expr_result(
    subst: &mut Subst,
    actual: Ty,
    expected: Ty,
) -> Result<(), TypeError> {
    if is_never(&subst.apply(&actual)) {
        return Ok(());
    }
    unify(subst, actual, expected)
}
