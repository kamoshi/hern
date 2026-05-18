//! Callable application and argument inference.
//!
//! This module infers call arguments, attaches dictionary wrappers for qualified
//! argument values, checks mutable-place capabilities, and unifies callable types.

use super::*;

impl Infer {
    pub(in crate::types::infer) fn infer_args(
        &mut self,
        env: &TypeEnv,
        args: &mut [Expr],
        arg_wrappers: &mut Vec<Option<ArgWrapper>>,
    ) -> Result<Vec<Ty>, SpannedTypeError> {
        self.infer_args_with_expected(env, args, arg_wrappers, None, 0)
    }

    fn infer_checked_args_with_expected(
        &mut self,
        env: &TypeEnv,
        args: &mut [Expr],
        arg_wrappers: &mut Vec<Option<ArgWrapper>>,
        expected_params: &[FuncParam],
        param_offset: usize,
    ) -> Result<Vec<Ty>, SpannedTypeError> {
        let arg_tys = self.infer_args_with_expected(
            env,
            args,
            arg_wrappers,
            Some(expected_params),
            param_offset,
        )?;
        self.check_mutable_place_args_from(
            env,
            args,
            &func_param_capabilities(expected_params),
            param_offset,
        )?;
        Ok(arg_tys)
    }

    fn infer_args_with_expected(
        &mut self,
        env: &TypeEnv,
        args: &mut [Expr],
        arg_wrappers: &mut Vec<Option<ArgWrapper>>,
        expected_params: Option<&[FuncParam]>,
        param_offset: usize,
    ) -> Result<Vec<Ty>, SpannedTypeError> {
        arg_wrappers.clear();
        let mut arg_tys = Vec::with_capacity(args.len());
        for (idx, arg) in args.iter_mut().enumerate() {
            let expected_param = expected_params.and_then(|params| params.get(param_offset + idx));
            let (arg_ty, wrapper) = self.infer_arg_and_wrapper(env, arg, expected_param)?;
            arg_wrappers.push(wrapper);
            arg_tys.push(arg_ty);
        }
        Ok(arg_tys)
    }

    fn infer_arg_and_wrapper(
        &mut self,
        env: &TypeEnv,
        arg: &mut Expr,
        expected_param: Option<&FuncParam>,
    ) -> Result<(Ty, Option<ArgWrapper>), SpannedTypeError> {
        let inferred = if let Some(expected_param) = expected_param
            && is_lambda_or_grouped_lambda(arg)
        {
            self.infer_expr_expected(env, arg, expected_param.ty.clone())?
        } else {
            self.infer_expr(env, arg)?
        };
        if has_mut_place_func_params(&self.subst.apply(&inferred))
            || self
                .metadata
                .callable_capabilities(arg.id)
                .is_some_and(|capabilities| {
                    capabilities
                        .param_capabilities
                        .iter()
                        .any(|capability| capability.is_mut_place())
                })
        {
            return Err(TypeError::MutableFunctionCapabilityMismatch.at(arg.span));
        }
        let (constraints, inner) = split_qualified(inferred);
        let arg_ty = self.subst.apply(&inner);
        let wrapper = if !constraints.is_empty() {
            let mut wrapper = ArgWrapper {
                dict_args: Vec::new(),
                pending_dict_args: Vec::new(),
            };
            attach_dict_args(
                env,
                &self.impls.active_dicts,
                &self.impls.known_schemes,
                &mut wrapper.dict_args,
                &mut wrapper.pending_dict_args,
                &mut self.constraints.pending,
                &constraints,
                &mut self.subst,
            )
            .map_err(|e| e.at(arg.span))?;
            Some(wrapper)
        } else {
            None
        };
        Ok((arg_ty, wrapper))
    }

    #[allow(clippy::too_many_arguments)]
    pub(in crate::types::infer) fn apply_scheme_callable(
        &mut self,
        env: &TypeEnv,
        args: &mut [Expr],
        arg_wrappers: &mut Vec<Option<ArgWrapper>>,
        scheme: &Scheme,
        leading_arg_tys: Vec<Ty>,
        leading_arg_span: Option<SourceSpan>,
        param_offset: usize,
        dict_args: &mut Vec<DictRef>,
        pending_dict_args: &mut Vec<PendingDictArg>,
    ) -> Result<AppliedSchemeCall, SpannedTypeError> {
        let instantiated = self.instantiate_scheme(scheme);
        let fresh_return = func_return_capability(&instantiated.ty) == ReturnCapability::FreshPlace;
        let callable_params = match &instantiated.ty {
            Ty::Func(params, _) => Some(params.clone()),
            _ => None,
        };
        let expected_params = callable_params.as_deref().unwrap_or(&[]);
        let mut arg_tys = leading_arg_tys;
        for (idx, leading_ty) in arg_tys.iter().enumerate() {
            if let Some(expected_param) = expected_params.get(idx) {
                unify(
                    &mut self.subst,
                    leading_ty.clone(),
                    expected_param.ty.clone(),
                )
                .map_err(|err| span_leading_arg_error(err, leading_arg_span))?;
            }
        }
        arg_tys.extend(self.infer_checked_args_with_expected(
            env,
            args,
            arg_wrappers,
            expected_params,
            param_offset,
        )?);
        let arity_span = args.first().map(|arg| arg.span).or(leading_arg_span);
        ensure_callable_arity(callable_params.as_deref(), arg_tys.len(), arity_span)?;
        let ret_ty = Ty::Var(self.fresh_var());
        let expected_params = expected_func_params(&instantiated.ty, arg_tys.clone());
        let expected_ret = expected_func_return(&instantiated.ty, ret_ty.clone());
        unify(
            &mut self.subst,
            instantiated.ty,
            Ty::Func(expected_params, expected_ret),
        )?;
        attach_dict_args(
            env,
            &self.impls.active_dicts,
            &self.impls.known_schemes,
            dict_args,
            pending_dict_args,
            &mut self.constraints.pending,
            &instantiated.constraints,
            &mut self.subst,
        )
        .map_err(TypeError::unspanned)?;
        Ok(AppliedSchemeCall {
            ret_ty: self.subst.apply(&ret_ty),
            arg_tys,
            fresh_return,
        })
    }

    #[allow(clippy::too_many_arguments)]
    pub(in crate::types::infer) fn apply_callable_type(
        &mut self,
        env: &TypeEnv,
        args: &mut [Expr],
        arg_wrappers: &mut Vec<Option<ArgWrapper>>,
        callable_ty: Ty,
        constraints: Vec<TraitConstraint>,
        leading_arg_tys: Vec<Ty>,
        leading_arg_span: Option<SourceSpan>,
        param_capabilities: Vec<ParamCapability>,
        param_offset: usize,
        dict_error_span: SourceSpan,
        dict_args: &mut Vec<DictRef>,
        pending_dict_args: &mut Vec<PendingDictArg>,
    ) -> Result<AppliedCall, SpannedTypeError> {
        let fresh_return = func_return_capability(&callable_ty) == ReturnCapability::FreshPlace;
        let callable_params = match &callable_ty {
            Ty::Func(params, _) => Some(params.clone()),
            _ => None,
        };
        let known_params = callable_params.as_deref().unwrap_or(&[]);
        let mut arg_tys = leading_arg_tys;
        for (idx, leading_ty) in arg_tys.iter().enumerate() {
            if let Some(expected_param) = known_params.get(idx) {
                unify(
                    &mut self.subst,
                    leading_ty.clone(),
                    expected_param.ty.clone(),
                )
                .map_err(|err| span_leading_arg_error(err, leading_arg_span))?;
            }
        }
        arg_tys.extend(self.infer_checked_args_with_expected(
            env,
            args,
            arg_wrappers,
            known_params,
            param_offset,
        )?);
        let arity_span = args.first().map(|arg| arg.span).or(leading_arg_span);
        ensure_callable_arity(callable_params.as_deref(), arg_tys.len(), arity_span)?;
        // Unknown callable shapes cannot supply per-parameter capabilities above,
        // so use the metadata gathered while inferring the callee expression.
        if callable_params.is_none() {
            self.check_mutable_place_args_from(env, args, &param_capabilities, param_offset)?;
        }
        let ret_ty = Ty::Var(self.fresh_var());
        let call_ty = Ty::Func(
            expected_func_params(&callable_ty, arg_tys.clone()),
            expected_func_return(&callable_ty, ret_ty.clone()),
        );
        unify(&mut self.subst, callable_ty, call_ty.clone())?;
        attach_dict_args(
            env,
            &self.impls.active_dicts,
            &self.impls.known_schemes,
            dict_args,
            pending_dict_args,
            &mut self.constraints.pending,
            &constraints,
            &mut self.subst,
        )
        .map_err(|err| err.at(dict_error_span))?;
        Ok(AppliedCall {
            ret_ty: self.subst.apply(&ret_ty),
            call_ty,
            fresh_return,
        })
    }

    pub(in crate::types::infer) fn infer_constrained_apply(
        &mut self,
        env: &TypeEnv,
        scheme: &Scheme,
        arg_tys: Vec<Ty>,
        dict_args: &mut Vec<DictRef>,
        pending_dict_args: &mut Vec<PendingDictArg>,
    ) -> Result<Ty, SpannedTypeError> {
        let instantiated = self.instantiate_scheme(scheme);
        let callable_params = match &instantiated.ty {
            Ty::Func(params, _) => Some(params.as_slice()),
            _ => None,
        };
        ensure_callable_arity(callable_params, arg_tys.len(), None)?;
        let ret_ty = Ty::Var(self.fresh_var());
        let expected_params = expected_func_params(&instantiated.ty, arg_tys);
        let expected_ret = expected_func_return(&instantiated.ty, ret_ty.clone());
        unify(
            &mut self.subst,
            instantiated.ty,
            Ty::Func(expected_params, expected_ret),
        )?;
        attach_dict_args(
            env,
            &self.impls.active_dicts,
            &self.impls.known_schemes,
            dict_args,
            pending_dict_args,
            &mut self.constraints.pending,
            &instantiated.constraints,
            &mut self.subst,
        )
        .map_err(TypeError::unspanned)?;
        Ok(self.subst.apply(&ret_ty))
    }
}

fn is_lambda_or_grouped_lambda(expr: &Expr) -> bool {
    match &expr.kind {
        ExprKind::Lambda { .. } => true,
        ExprKind::Grouped(inner) => is_lambda_or_grouped_lambda(inner),
        _ => false,
    }
}

fn ensure_callable_arity(
    expected_params: Option<&[FuncParam]>,
    got: usize,
    span: Option<SourceSpan>,
) -> Result<(), SpannedTypeError> {
    if let Some(expected_params) = expected_params
        && expected_params.len() != got
    {
        let err = TypeError::ArityMismatch {
            expected: expected_params.len(),
            got,
        };
        return Err(match span {
            Some(span) => err.at(span),
            None => err.into(),
        });
    }
    Ok(())
}

fn span_leading_arg_error(err: TypeError, span: Option<SourceSpan>) -> SpannedTypeError {
    match span {
        Some(span) => err.at(span),
        None => err.into(),
    }
}

fn split_qualified(ty: Ty) -> (Vec<TraitConstraint>, Ty) {
    match ty {
        Ty::Qualified(constraints, inner) => (constraints, *inner),
        other => (Vec::new(), other),
    }
}
