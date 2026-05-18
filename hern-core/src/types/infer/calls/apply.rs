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
            && matches!(arg.kind, ExprKind::Lambda { .. })
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
                &self.impls.known_dicts,
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
        param_offset: usize,
        dict_args: &mut Vec<DictRef>,
        pending_dict_args: &mut Vec<PendingDictArg>,
    ) -> Result<AppliedSchemeCall, SpannedTypeError> {
        let instantiated = self.instantiate_scheme(scheme);
        let expected_params = match &instantiated.ty {
            Ty::Func(params, _) => params.clone(),
            _ => Vec::new(),
        };
        let mut arg_tys = leading_arg_tys;
        for (idx, leading_ty) in arg_tys.iter().enumerate() {
            if let Some(expected_param) = expected_params.get(idx) {
                unify(
                    &mut self.subst,
                    leading_ty.clone(),
                    expected_param.ty.clone(),
                )?;
            }
        }
        arg_tys.extend(self.infer_checked_args_with_expected(
            env,
            args,
            arg_wrappers,
            &expected_params,
            param_offset,
        )?);
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
            &self.impls.known_dicts,
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
        param_capabilities: Vec<ParamCapability>,
        param_offset: usize,
        dict_error_span: SourceSpan,
        dict_args: &mut Vec<DictRef>,
        pending_dict_args: &mut Vec<PendingDictArg>,
    ) -> Result<AppliedCall, SpannedTypeError> {
        let fresh_return = func_return_capability(&callable_ty) == ReturnCapability::FreshPlace;
        let expected_params = match &callable_ty {
            Ty::Func(params, _) => params.clone(),
            _ => Vec::new(),
        };
        let mut arg_tys = leading_arg_tys;
        for (idx, leading_ty) in arg_tys.iter().enumerate() {
            if let Some(expected_param) = expected_params.get(idx) {
                unify(
                    &mut self.subst,
                    leading_ty.clone(),
                    expected_param.ty.clone(),
                )?;
            }
        }
        arg_tys.extend(self.infer_checked_args_with_expected(
            env,
            args,
            arg_wrappers,
            &expected_params,
            param_offset,
        )?);
        if expected_params.is_empty() {
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
            &self.impls.known_dicts,
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
            &self.impls.known_dicts,
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

fn split_qualified(ty: Ty) -> (Vec<TraitConstraint>, Ty) {
    match ty {
        Ty::Qualified(constraints, inner) => (constraints, *inner),
        other => (Vec::new(), other),
    }
}
