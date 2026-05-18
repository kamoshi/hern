//! Trait dictionary dispatch for calls and operators.
//!
//! This module selects concrete dictionaries, builds pending trait-method
//! obligations, and handles structural dispatch such as tuple equality.

use super::*;

impl Infer {
    #[allow(clippy::too_many_arguments)]
    pub(in crate::types::infer) fn resolve_multi_param_trait_dispatch(
        &mut self,
        env: &TypeEnv,
        trait_name: &str,
        method_name: &str,
        trait_args: Vec<Ty>,
        determinant_indexes: Vec<usize>,
        method_arg_tys: Vec<Ty>,
        ret_ty: Ty,
        resolved_callee: &mut Option<ResolvedCallee>,
        pending_trait_method: &mut Option<(PendingDictArg, String)>,
        concrete_dict_expect: &'static str,
    ) -> Result<Option<Ty>, SpannedTypeError> {
        if let Some(dict) = resolve_concrete_from_args_unifying(
            trait_name,
            &trait_args,
            &determinant_indexes,
            env,
            &self.impls.known_dicts,
            &self.impls.known_schemes,
            &mut self.subst,
        ) {
            let dict_name = dict_ref_concrete_name(&dict)
                .expect(concrete_dict_expect)
                .to_string();
            if let Some(dict_scheme) = env
                .get(&dict_name)
                .map(|info| info.scheme.clone())
                .or_else(|| self.impls.known_schemes.get(&dict_name).cloned())
            {
                let dict_ty = self.instantiate(&dict_scheme);
                let dict_method_ty = record_field_ty(&self.subst.apply(&dict_ty), method_name)
                    .ok_or_else(|| TypeError::UnknownTraitMethod {
                        trait_name: trait_name.to_string(),
                        method: method_name.to_string(),
                    })?;
                let checked_ret = Ty::Var(self.fresh_var());
                unify(
                    &mut self.subst,
                    dict_method_ty,
                    Ty::Func(
                        value_func_params(method_arg_tys),
                        value_func_return(checked_ret.clone()),
                    ),
                )?;
                unify(&mut self.subst, ret_ty.clone(), checked_ret)?;
            }
            *resolved_callee = Some(ResolvedCallee::DictMethod {
                dict,
                method: method_name.to_string(),
            });
            return Ok(Some(self.subst.apply(&ret_ty)));
        }

        if let Some(var) = primary_trait_var(&trait_args, &determinant_indexes) {
            let constraint = TraitConstraint::predicate(
                trait_name,
                trait_args.clone(),
                var,
                determinant_indexes.clone(),
            );
            self.constraints.pending.push(constraint);
            let pending = PendingDictArg {
                var,
                trait_name: trait_name.to_string(),
                args: trait_args,
                determinant_indexes,
            };
            *pending_trait_method = Some((pending, method_name.to_string()));
            return Ok(Some(self.subst.apply(&ret_ty)));
        }

        Ok(None)
    }

    #[allow(clippy::too_many_arguments)]
    pub(in crate::types::infer) fn resolve_operator_dispatch(
        &mut self,
        env: &TypeEnv,
        trait_name: &str,
        op: &str,
        resolved_target: &Ty,
        resolved_op: &mut Option<ResolvedCallee>,
        pending_op: &mut Option<PendingDictArg>,
        _dict_args: &mut Vec<DictRef>,
        _pending_dict_args: &mut Vec<PendingDictArg>,
    ) -> Result<(), SpannedTypeError> {
        match self
            .resolve_trait_dict(env, trait_name, resolved_target.clone())
            .map_err(SpannedTypeError::from)?
        {
            DictResolution::Resolved(dict) => {
                *resolved_op = Some(ResolvedCallee::DictMethod {
                    dict,
                    method: op.to_string(),
                });
            }
            DictResolution::Pending(pending) => {
                *pending_op = Some(pending);
            }
        }
        Ok(())
    }

    fn resolve_trait_dict(
        &mut self,
        env: &TypeEnv,
        trait_name: &str,
        target: Ty,
    ) -> Result<DictResolution, TypeError> {
        let target = self.subst.apply(&target);
        if let Ty::Var(var) = target {
            let constraint = TraitConstraint::unary(var, trait_name.to_string());
            self.constraints.pending.push(constraint.clone());
            return Ok(DictResolution::Pending(PendingDictArg {
                var,
                trait_name: trait_name.to_string(),
                args: vec![Ty::Var(var)],
                determinant_indexes: vec![0],
            }));
        }
        if let Some(dict) = self.resolve_structural_dict(env, trait_name, &target)? {
            return Ok(DictResolution::Resolved(dict));
        }
        resolve_concrete_dict_ref(
            trait_name,
            &target,
            env,
            &self.impls.known_dicts,
            &self.impls.known_schemes,
        )
        .map(DictResolution::Resolved)
        .ok_or_else(|| TypeError::MissingTraitImpl {
            trait_name: trait_name.to_string(),
            impl_target: format!("{}", target),
        })
    }

    fn resolve_structural_dict(
        &mut self,
        env: &TypeEnv,
        trait_name: &str,
        target: &Ty,
    ) -> Result<Option<DictRef>, TypeError> {
        match (trait_name, target) {
            ("Eq", Ty::Tuple(items)) => Ok(Some(DictRef::Structural(StructuralDictRef {
                trait_name: "Eq".to_string(),
                target: DictTarget::Tuple(items.len()),
                args: items
                    .iter()
                    .map(|item| self.resolve_eq_child_dict(env, item))
                    .collect::<Result<_, _>>()?,
            }))),
            _ => Ok(None),
        }
    }

    fn resolve_eq_child_dict(&mut self, env: &TypeEnv, ty: &Ty) -> Result<DictRef, TypeError> {
        match self.subst.apply(ty) {
            Ty::Tuple(items) => self
                .resolve_structural_dict(env, "Eq", &Ty::Tuple(items))?
                .ok_or_else(|| TypeError::MissingTraitImpl {
                    trait_name: "Eq".to_string(),
                    impl_target: format!("{}", ty),
                }),
            Ty::Var(var) => {
                let constraint = TraitConstraint::unary(var, "Eq");
                self.constraints.pending.push(constraint.clone());
                Ok(DictRef::Param(dict_param_name(&constraint)))
            }
            resolved => {
                let target_keys = trait_impl_target_keys_from_ty(&resolved);
                if target_keys.is_empty() {
                    return Err(TypeError::MissingTraitImpl {
                        trait_name: "Eq".to_string(),
                        impl_target: format!("{}", resolved),
                    });
                }
                resolve_concrete_dict_ref(
                    "Eq",
                    &resolved,
                    env,
                    &self.impls.known_dicts,
                    &self.impls.known_schemes,
                )
                .ok_or_else(|| TypeError::MissingTraitImpl {
                    trait_name: "Eq".to_string(),
                    impl_target: format!("{}", resolved),
                })
            }
        }
    }

    #[allow(clippy::too_many_arguments)]
    pub(in crate::types::infer) fn resolve_trait_method_call(
        &mut self,
        env: &TypeEnv,
        args: &mut [Expr],
        arg_wrappers: &mut Vec<Option<ArgWrapper>>,
        resolved_callee: &mut Option<ResolvedCallee>,
        pending_trait_method: &mut Option<(PendingDictArg, String)>,
        trait_def: TraitDef,
        method: TraitMethod,
        context: &str,
    ) -> Result<Ty, SpannedTypeError> {
        let trait_name = trait_def.name.clone();
        let method_name = method.name.clone();

        if trait_def.params.len() > 1 || !trait_def.fundeps.is_empty() {
            return self.resolve_multi_param_trait_method_call(
                env,
                args,
                arg_wrappers,
                resolved_callee,
                pending_trait_method,
                trait_def,
                method,
                context,
            );
        }

        // Decide dispatch strategy based on whether the first parameter's type
        // contains the trait's HKT variable (e.g. `'f` in `map(fa: 'f('a), ...)`).
        // If it does, we can read the impl target directly from the first argument's
        // concrete type.  If not (e.g. `pure(a: 'a)`), the target is only known from
        // context, so we fall back to abstract unification and a pending marker.
        let trait_param = primary_param_or_panic(&trait_def);
        let first_param_has_trait_var = method
            .params
            .first()
            .map(|(_, ty)| type_contains_var(ty, trait_param))
            .unwrap_or(false);

        let arg_tys = self.infer_args(env, args, arg_wrappers)?;
        if arg_tys.len() != method.params.len() {
            return Err(TypeError::ArityMismatch {
                expected: method.params.len(),
                got: arg_tys.len(),
            }
            .into());
        }

        if first_param_has_trait_var {
            // ── First-arg dispatch ────────────────────────────────────────────
            // Extract the impl target from the first argument's concrete type,
            // then look up the concrete dict and unify against its method type.
            // This avoids abstract HKT unification, which breaks for multi-arg
            // type constructors like `Result('a, 'e)` vs `'f('a)`.
            let resolved_target = self.subst.apply(&arg_tys[0]);
            let target_keys = trait_impl_target_keys_from_ty(&resolved_target);
            if target_keys.is_empty() {
                if let Some(target_var) = variable_trait_target(&resolved_target) {
                    let (ret_ty, resolved_var) = self.check_trait_method_signature_allow_pending(
                        &trait_def, &method, arg_tys, context,
                    )?;
                    let pending = PendingDictArg {
                        var: resolved_var.unwrap_or(target_var),
                        trait_name: trait_name.clone(),
                        args: vec![Ty::Var(resolved_var.unwrap_or(target_var))],
                        determinant_indexes: vec![0],
                    };
                    self.constraints.pending.push(TraitConstraint::unary(
                        pending.var,
                        pending.trait_name.clone(),
                    ));
                    *pending_trait_method = Some((pending, method_name));
                    return Ok(self.subst.apply(&ret_ty));
                }
                return Err(TypeError::UnresolvedTrait {
                    context: context.to_string(),
                    trait_name: trait_name.clone(),
                }
                .into());
            }
            let Some(dict) = resolve_concrete_dict_ref(
                &trait_name,
                &resolved_target,
                env,
                &self.impls.known_dicts,
                &self.impls.known_schemes,
            ) else {
                return Err(TypeError::MissingTraitImpl {
                    trait_name: trait_name.clone(),
                    impl_target: format!("{}", resolved_target),
                }
                .into());
            };
            let dict_name = dict_ref_concrete_name(&dict)
                .expect("non-structural trait method dict should have a concrete name")
                .to_string();

            let dict_scheme = env
                .get(&dict_name)
                .map(|info| info.scheme.clone())
                .or_else(|| self.impls.known_schemes.get(&dict_name).cloned());
            let ret_ty = if let Some(dict_scheme) = dict_scheme {
                let dict_ty = self.instantiate(&dict_scheme);
                let method_ty = record_field_ty(&self.subst.apply(&dict_ty), &method_name)
                    .ok_or_else(|| TypeError::UnknownTraitMethod {
                        trait_name: trait_name.clone(),
                        method: method_name.clone(),
                    })?;
                let ret_ty = Ty::Var(self.fresh_var());
                unify(
                    &mut self.subst,
                    method_ty,
                    Ty::Func(
                        value_func_params(arg_tys),
                        value_func_return(ret_ty.clone()),
                    ),
                )?;
                ret_ty
            } else {
                self.check_trait_method_signature(&trait_def, &method, arg_tys, context)?
            };

            *resolved_callee = Some(ResolvedCallee::DictMethod {
                dict,
                method: method_name.clone(),
            });
            Ok(self.subst.apply(&ret_ty))
        } else {
            // ── Abstract unification + pending dispatch ───────────────────────
            // Used for methods like `pure(a: 'a) -> 'f('a)` where the first
            // parameter doesn't reveal the impl target.  We unify the value
            // arguments against the abstract method signature, then defer target
            // resolution to `resolve_dict_uses_expr` once the outer context has
            // pinned the type variable.
            let mut param_vars: HashMap<String, TyVar> = HashMap::new();
            let target_var = self.fresh_var();
            param_vars.insert(trait_param.to_string(), target_var);

            let method_param_tys: Vec<Ty> = method
                .params
                .iter()
                .map(|(_, p_ty)| self.ast_to_ty_with_vars(p_ty, &mut param_vars))
                .collect::<Result<_, _>>()?;
            let ret_ty = self.ast_to_ty_with_vars(&method.ret_type, &mut param_vars)?;

            for (arg_ty, param_ty) in arg_tys.into_iter().zip(method_param_tys) {
                unify(&mut self.subst, arg_ty, param_ty)?;
            }

            let resolved_target = self.subst.apply(&Ty::Var(target_var));
            let target_keys = trait_impl_target_keys_from_ty(&resolved_target);
            if target_keys.is_empty() {
                match resolved_target {
                    Ty::Var(v) => {
                        let pending = PendingDictArg {
                            var: v,
                            trait_name: trait_name.clone(),
                            args: vec![Ty::Var(v)],
                            determinant_indexes: vec![0],
                        };
                        self.constraints.pending.push(TraitConstraint::unary(
                            pending.var,
                            pending.trait_name.clone(),
                        ));
                        *pending_trait_method = Some((pending, method_name));
                        Ok(self.subst.apply(&ret_ty))
                    }
                    _ => Err(TypeError::MissingTraitImpl {
                        trait_name: trait_name.clone(),
                        impl_target: format!("{}", resolved_target),
                    }
                    .into()),
                }
            } else {
                match resolve_concrete_dict_ref(
                    &trait_name,
                    &resolved_target,
                    env,
                    &self.impls.known_dicts,
                    &self.impls.known_schemes,
                ) {
                    Some(dict) => {
                        *resolved_callee = Some(ResolvedCallee::DictMethod {
                            dict,
                            method: method_name.clone(),
                        });
                        Ok(self.subst.apply(&ret_ty))
                    }
                    None => Err(TypeError::MissingTraitImpl {
                        trait_name: trait_name.clone(),
                        impl_target: format!("{}", resolved_target),
                    }
                    .into()),
                }
            }
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn resolve_multi_param_trait_method_call(
        &mut self,
        env: &TypeEnv,
        args: &mut [Expr],
        arg_wrappers: &mut Vec<Option<ArgWrapper>>,
        resolved_callee: &mut Option<ResolvedCallee>,
        pending_trait_method: &mut Option<(PendingDictArg, String)>,
        trait_def: TraitDef,
        method: TraitMethod,
        context: &str,
    ) -> Result<Ty, SpannedTypeError> {
        let trait_name = trait_def.name.clone();
        let method_name = method.name.clone();
        let arg_tys = self.infer_args(env, args, arg_wrappers)?;
        if arg_tys.len() != method.params.len() {
            return Err(TypeError::ArityMismatch {
                expected: method.params.len(),
                got: arg_tys.len(),
            }
            .into());
        }

        let mut param_vars: HashMap<String, TyVar> = HashMap::new();
        let trait_param_vars = trait_def
            .params
            .iter()
            .map(|param| {
                let var = self.fresh_var();
                param_vars.insert(param.clone(), var);
                var
            })
            .collect::<Vec<_>>();
        let method_param_tys: Vec<Ty> = method
            .params
            .iter()
            .map(|(_, p_ty)| self.ast_to_ty_with_vars(p_ty, &mut param_vars))
            .collect::<Result<_, _>>()?;
        let ret_ty = self.ast_to_ty_with_vars(&method.ret_type, &mut param_vars)?;

        for (arg_ty, param_ty) in arg_tys.iter().cloned().zip(method_param_tys) {
            unify(&mut self.subst, arg_ty, param_ty)?;
        }

        let trait_args = trait_param_vars
            .iter()
            .map(|var| self.subst.apply(&Ty::Var(*var)))
            .collect::<Vec<_>>();
        let determinant_indexes = trait_dict_indexes(&trait_def);
        if let Some(ret_ty) = self.resolve_multi_param_trait_dispatch(
            env,
            &trait_name,
            method_name.as_str(),
            trait_args,
            determinant_indexes,
            arg_tys,
            ret_ty,
            resolved_callee,
            pending_trait_method,
            "multi-parameter trait dictionaries should be concrete",
        )? {
            return Ok(ret_ty);
        }

        Err(TypeError::UnresolvedTrait {
            context: context.to_string(),
            trait_name,
        }
        .into())
    }

    fn check_trait_method_signature(
        &mut self,
        trait_def: &TraitDef,
        method: &TraitMethod,
        arg_tys: Vec<Ty>,
        context: &str,
    ) -> Result<Ty, SpannedTypeError> {
        let mut param_vars = HashMap::new();
        let target_var = self.fresh_var();
        let trait_param = primary_param_or_panic(trait_def);
        param_vars.insert(trait_param.to_string(), target_var);
        let method_param_tys: Vec<Ty> = method
            .params
            .iter()
            .map(|(_, p_ty)| self.ast_to_ty_with_vars(p_ty, &mut param_vars))
            .collect::<Result<_, _>>()?;
        let ret_ty = self.ast_to_ty_with_vars(&method.ret_type, &mut param_vars)?;
        for (arg_ty, expected_ty) in arg_tys.into_iter().zip(method_param_tys) {
            unify(&mut self.subst, expected_ty, arg_ty)?;
        }
        let resolved_target = self.subst.apply(&Ty::Var(target_var));
        if trait_impl_target_keys_from_ty(&resolved_target).is_empty() {
            return Err(TypeError::UnresolvedTrait {
                context: context.to_string(),
                trait_name: trait_def.name.clone(),
            }
            .into());
        }
        Ok(ret_ty)
    }

    fn check_trait_method_signature_allow_pending(
        &mut self,
        trait_def: &TraitDef,
        method: &TraitMethod,
        arg_tys: Vec<Ty>,
        context: &str,
    ) -> Result<(Ty, Option<TyVar>), SpannedTypeError> {
        let mut param_vars = HashMap::new();
        let target_var = self.fresh_var();
        let trait_param = primary_param_or_panic(trait_def);
        param_vars.insert(trait_param.to_string(), target_var);
        let method_param_tys: Vec<Ty> = method
            .params
            .iter()
            .map(|(_, p_ty)| self.ast_to_ty_with_vars(p_ty, &mut param_vars))
            .collect::<Result<_, _>>()?;
        let ret_ty = self.ast_to_ty_with_vars(&method.ret_type, &mut param_vars)?;
        for (arg_ty, expected_ty) in arg_tys.into_iter().zip(method_param_tys) {
            unify(&mut self.subst, expected_ty, arg_ty)?;
        }
        match self.subst.apply(&Ty::Var(target_var)) {
            Ty::Var(var) => Ok((ret_ty, Some(var))),
            other if trait_impl_target_keys_from_ty(&other).is_empty() => {
                Err(TypeError::UnresolvedTrait {
                    context: context.to_string(),
                    trait_name: trait_def.name.clone(),
                }
                .into())
            }
            _ => Ok((ret_ty, None)),
        }
    }
}

fn variable_trait_target(ty: &Ty) -> Option<TyVar> {
    match ty {
        Ty::Var(var) => Some(*var),
        Ty::App(con, _) => variable_trait_target(con),
        Ty::Qualified(_, inner) => variable_trait_target(inner),
        Ty::Int
        | Ty::Float
        | Ty::Unit
        | Ty::Never
        | Ty::Con(_)
        | Ty::Tuple(_)
        | Ty::Func(_, _)
        | Ty::Record(_) => None,
    }
}
