//! Recursive block inference.
//!
//! Recursive function groups are checked in two phases: introduce provisional
//! schemes so names can refer to each other, then infer bodies and unify them
//! with the declared recursive surface.

use super::*;

pub(super) struct RecFnInfo {
    pub(super) name: String,
    pub(super) fn_ty: Ty,
    pub(super) param_tys: Vec<Ty>,
    pub(super) ret_ty: Ty,
    pub(super) fn_ret: FuncReturn,
    pub(super) has_explicit_return: bool,
    pub(super) initial_constraints: Vec<TraitConstraint>,
    pub(super) constraints: Vec<TraitConstraint>,
    pub(super) owned_constraints: Vec<TraitConstraint>,
    pub(super) scheme: Option<Scheme>,
}

impl Infer {
    pub(super) fn infer_rec_block(
        &mut self,
        env: &mut TypeEnv,
        stmts: &mut [Stmt],
    ) -> Result<(), SpannedTypeError> {
        self.validate_rec_group_function_names(stmts)?;
        let ambient = self.current_level;
        let mut rec_infos = self.with_child_level(|this| {
            let mut rec_env = env.clone();
            let mut infos = Vec::new();

            for stmt in stmts.iter() {
                let Stmt::Fn {
                    name,
                    params,
                    ret_type,
                    type_bounds,
                    ..
                } = stmt
                else {
                    unreachable!("parser restricts rec blocks to functions")
                };
                let info = this.prepare_rec_fn_info(name.clone(), params, ret_type, type_bounds)?;
                rec_env.insert(
                    name.clone(),
                    EnvInfo::immutable(Scheme::mono(info.fn_ty.clone())),
                );
                infos.push(info);
            }

            for (stmt, info) in stmts.iter_mut().zip(infos.iter_mut()) {
                let Stmt::Fn { params, body, .. } = stmt else {
                    unreachable!("rec block was validated to contain only functions")
                };
                let mut body_env = rec_env.clone();
                for (param, p_ty) in params.iter().zip(info.param_tys.iter()) {
                    if !is_irrefutable_param(&param.pat, &this.types.variant_env) {
                        return Err(TypeError::RefutableParamPattern.at(body.span));
                    }
                    this.check_param_pattern(
                        &param.pat,
                        p_ty.clone(),
                        &mut body_env,
                        param.mut_place,
                    )?;
                }
                let (_, constraints) = this.with_pending_constraints_scope(
                    info.initial_constraints.clone(),
                    |this| {
                        let body_ty = this.with_fn_return_scope(info.fn_ret.clone(), |this| {
                            if info.has_explicit_return {
                                this.infer_expr_expected(&body_env, body, info.ret_ty.clone())
                            } else {
                                this.infer_expr(&body_env, body)
                            }
                        })?;
                        unify_expr_result(&mut this.subst, body_ty.clone(), info.ret_ty.clone())
                            .map_err(|err| err.at(body.span))?;
                        if !matches!(this.subst.apply(&body_ty), Ty::Never) {
                            this.check_fresh_return_expr(body, &info.fn_ret)?;
                        }
                        Ok(())
                    },
                )?;
                info.constraints = constraints;
            }

            propagate_rec_block_constraints(stmts, &mut infos);

            Ok(infos)
        })?;

        for info in &mut rec_infos {
            let finalized = self.finalize_constraints_at(
                env,
                info.fn_ty.clone(),
                std::mem::take(&mut info.constraints),
                ambient,
            );
            self.constraints.pending.extend(finalized.bubbled.clone());
            info.owned_constraints = finalized.owned.clone();
            info.scheme = Some(finalized.scheme);
        }

        for info in &rec_infos {
            if info.owned_constraints.is_empty() {
                continue;
            }
            for stmt in stmts.iter_mut() {
                let Stmt::Fn { body, .. } = stmt else {
                    unreachable!("rec block was validated to contain only functions")
                };
                attach_owned_dicts_to_recursive_self_calls(
                    body,
                    &info.name,
                    &info.owned_constraints,
                );
            }
        }

        for (stmt, info) in stmts.iter_mut().zip(rec_infos.iter()) {
            let Stmt::Fn {
                name,
                name_span,
                body,
                dict_params,
                ..
            } = stmt
            else {
                unreachable!("rec block was validated to contain only functions")
            };
            *dict_params = info.owned_constraints.iter().map(dict_param_name).collect();
            let resolver = |p: &PendingDictArg| {
                resolve_local_or_concrete(
                    p,
                    &info.owned_constraints,
                    env,
                    &self.impls.known_dicts,
                    &self.impls.known_schemes,
                    &self.subst,
                )
            };
            resolve_dict_uses_expr(body, &resolver, false)?;
            let scheme = info
                .scheme
                .clone()
                .expect("rec function should have a finalized scheme");
            env.insert(name.clone(), EnvInfo::immutable(scheme.clone()));
            self.metadata.record_definition_scheme(*name_span, scheme);
        }

        Ok(())
    }

    pub(super) fn validate_rec_group_function_names(
        &self,
        stmts: &[Stmt],
    ) -> Result<(), SpannedTypeError> {
        let mut seen: HashMap<&str, SourceSpan> = HashMap::new();
        for stmt in stmts {
            let Stmt::Fn {
                name, name_span, ..
            } = stmt
            else {
                unreachable!("parser restricts recursive groups to functions")
            };
            if seen.insert(name.as_str(), *name_span).is_some() {
                return Err(TypeError::DuplicateFunctionInGroup(name.clone()).at(*name_span));
            }
        }
        Ok(())
    }

    pub(super) fn prepare_rec_fn_info(
        &mut self,
        name: String,
        params: &[Param],
        ret_type: &Option<TypeReturn>,
        type_bounds: &[TypeBound],
    ) -> Result<RecFnInfo, SpannedTypeError> {
        let mut param_vars = HashMap::new();
        let initial_constraints =
            self.collect_type_bound_constraints(&mut param_vars, type_bounds)?;
        let mut param_tys = Vec::new();
        for param in params {
            let p_ty = match &param.ty {
                Some(t) => self.ast_to_ty_with_vars(t, &mut param_vars)?,
                None => self.fresh_ty(),
            };
            param_tys.push(p_ty);
        }
        let ret_ty = match ret_type {
            Some(t) => self.ast_to_ty_with_vars(&t.ty, &mut param_vars)?,
            None => self.fresh_ty(),
        };
        let fn_ret = func_return_from_annotation(ret_type, ret_ty.clone());
        let fn_ty = Ty::Func(
            func_params_from_params(params, param_tys.clone()),
            fn_ret.clone(),
        );
        Ok(RecFnInfo {
            name,
            fn_ty,
            param_tys,
            ret_ty,
            fn_ret,
            has_explicit_return: ret_type.is_some(),
            initial_constraints,
            constraints: Vec::new(),
            owned_constraints: Vec::new(),
            scheme: None,
        })
    }
}
