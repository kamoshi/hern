use super::*;

pub(super) struct AppliedCall {
    pub(super) ret_ty: Ty,
    pub(super) call_ty: Ty,
    pub(super) fresh_return: bool,
}

pub(super) struct AppliedSchemeCall {
    pub(super) ret_ty: Ty,
    pub(super) arg_tys: Vec<Ty>,
    pub(super) fresh_return: bool,
}

impl Infer {
    #[allow(clippy::too_many_arguments)]
    pub(super) fn resolve_operator_dispatch(
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
            let constraint = TraitConstraint {
                var,
                trait_name: trait_name.to_string(),
            };
            self.pending_constraints.push(constraint.clone());
            return Ok(DictResolution::Pending(PendingDictArg {
                var,
                trait_name: trait_name.to_string(),
            }));
        }
        if let Some(dict) = self.resolve_structural_dict(env, trait_name, &target)? {
            return Ok(DictResolution::Resolved(dict));
        }
        resolve_concrete_dict_ref(
            trait_name,
            &target,
            env,
            &self.known_impl_dicts,
            &self.known_impl_schemes,
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
                let constraint = TraitConstraint {
                    var,
                    trait_name: "Eq".to_string(),
                };
                self.pending_constraints.push(constraint.clone());
                Ok(DictRef::Param(dict_param_name(&constraint)))
            }
            resolved => {
                let target_keys = trait_impl_target_keys_from_ty(&resolved);
                if target_keys.is_empty() {
                    return Err(TypeError::MissingTraitImpl {
                        trait_name: "Eq".to_string(),
                        impl_target: format!("{}", resolved),
                    }
                    .into());
                }
                resolve_concrete_dict_ref(
                    "Eq",
                    &resolved,
                    env,
                    &self.known_impl_dicts,
                    &self.known_impl_schemes,
                )
                .ok_or_else(|| {
                    TypeError::MissingTraitImpl {
                        trait_name: "Eq".to_string(),
                        impl_target: format!("{}", resolved),
                    }
                    .into()
                })
            }
        }
    }

    pub(super) fn resolve_trait_method_call(
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

        // Decide dispatch strategy based on whether the first parameter's type
        // contains the trait's HKT variable (e.g. `'f` in `map(fa: 'f('a), ...)`).
        // If it does, we can read the impl target directly from the first argument's
        // concrete type.  If not (e.g. `pure(a: 'a)`), the target is only known from
        // context, so we fall back to abstract unification and a pending marker.
        let first_param_has_trait_var = method
            .params
            .first()
            .map(|(_, ty)| type_contains_var(ty, &trait_def.param))
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
                    };
                    self.pending_constraints.push(TraitConstraint {
                        var: pending.var,
                        trait_name: pending.trait_name.clone(),
                    });
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
                &self.known_impl_dicts,
                &self.known_impl_schemes,
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
                .or_else(|| self.known_impl_schemes.get(&dict_name).cloned());
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
            param_vars.insert(trait_def.param.clone(), target_var);

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
                        };
                        self.pending_constraints.push(TraitConstraint {
                            var: pending.var,
                            trait_name: pending.trait_name.clone(),
                        });
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
                    &self.known_impl_dicts,
                    &self.known_impl_schemes,
                ) {
                    Some(dict) => {
                        *resolved_callee = Some(ResolvedCallee::DictMethod {
                            dict,
                            method: method_name.clone(),
                        });
                        Ok(self.subst.apply(&ret_ty))
                    }
                    None => {
                        return Err(TypeError::MissingTraitImpl {
                            trait_name: trait_name.clone(),
                            impl_target: format!("{}", resolved_target),
                        }
                        .into());
                    }
                }
            }
        }
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
        param_vars.insert(trait_def.param.clone(), target_var);
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
        param_vars.insert(trait_def.param.clone(), target_var);
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

    #[allow(clippy::too_many_arguments)]
    pub(super) fn resolve_associated_call(
        &mut self,
        env: &TypeEnv,
        call_expr_id: NodeId,
        callee_id: NodeId,
        target: &Type,
        target_span: SourceSpan,
        member: &str,
        member_span: SourceSpan,
        args: &mut [Expr],
        arg_wrappers: &mut Vec<Option<ArgWrapper>>,
        resolved_callee: &mut Option<ResolvedCallee>,
        dict_args: &mut Vec<DictRef>,
        pending_dict_args: &mut Vec<PendingDictArg>,
    ) -> Result<Ty, SpannedTypeError> {
        let target_name = inherent_impl_target_key_from_ast(target, &self.declared_types)
            .map_err(|err| err.at(target_span))?;
        let method_info = self
            .inherent_methods
            .get(&target_name)
            .and_then(|methods| methods.get(member))
            .or_else(|| {
                self.scoped_inherent_methods
                    .get(&target_name)
                    .and_then(|methods| methods.get(member))
            })
            .cloned()
            .ok_or_else(|| {
                TypeError::UnknownAssociatedFunction {
                    target: target_name.clone(),
                    function: member.to_string(),
                }
                .at(member_span)
            })?;
        let method_ty = self.instantiate_value(&method_info.scheme);
        self.record_symbol_type(callee_id, method_ty.clone());

        if method_info.has_receiver {
            return Err(TypeError::MethodRequiresReceiver {
                target: target_name,
                method: member.to_string(),
            }
            .at(member_span));
        }

        let applied = self.apply_scheme_callable(
            env,
            args,
            arg_wrappers,
            &method_info.scheme,
            Vec::new(),
            0,
            dict_args,
            pending_dict_args,
        )?;
        let return_capability = scheme_return_capability(&method_info.scheme);
        self.record_symbol_type(
            callee_id,
            Ty::Func(
                expected_func_params(&method_ty, applied.arg_tys),
                FuncReturn {
                    ty: Box::new(applied.ret_ty.clone()),
                    capability: return_capability,
                },
            ),
        );
        *resolved_callee = Some(method_info.resolved_callee);
        if applied.fresh_return && call_expr_id != NO_NODE_ID {
            self.metadata.mark_fresh_place(call_expr_id);
        }
        Ok(applied.ret_ty)
    }

    #[allow(clippy::too_many_arguments)]
    pub(super) fn resolve_receiver_call(
        &mut self,
        env: &TypeEnv,
        call_expr_id: NodeId,
        callee_id: NodeId,
        receiver: &mut Box<Expr>,
        method_name: &str,
        args: &mut [Expr],
        is_method_call: &mut bool,
        arg_wrappers: &mut Vec<Option<ArgWrapper>>,
        resolved_callee: &mut Option<ResolvedCallee>,
        dict_args: &mut Vec<DictRef>,
        pending_dict_args: &mut Vec<PendingDictArg>,
        expected_ret: Option<Ty>,
    ) -> Result<Ty, SpannedTypeError> {
        let inferred_receiver_ty = self.infer_expr(env, receiver)?;
        let receiver_ty = self.subst.apply(&inferred_receiver_ty);
        if let ExprKind::Ident(base_name) = &receiver.kind {
            if let Some(module_name) = self.import_bindings.get(base_name)
                && let Some(scheme) = self
                    .import_schemes
                    .get(module_name)
                    .and_then(|members| members.get(method_name))
                && matches!(scheme.ty, Ty::Func(_, _))
            {
                self.record_callable_capabilities(callee_id, scheme_param_capabilities(scheme));
            } else if let Some(param_capabilities) = self
                .record_field_callables
                .get(base_name)
                .and_then(|fields| fields.get(method_name))
                .cloned()
            {
                self.record_callable_capabilities(callee_id, param_capabilities);
            }
        }

        if let Some(mut field_ty) = record_field_ty(&receiver_ty, method_name) {
            if let Ty::Qualified(constraints, inner) = field_ty {
                attach_dict_args(
                    env,
                    &self.known_impl_dicts,
                    &self.known_impl_schemes,
                    dict_args,
                    pending_dict_args,
                    &mut self.pending_constraints,
                    &constraints,
                    &self.subst,
                )
                .map_err(|e| e.at(receiver.span))?;
                field_ty = *inner;
            }
            self.record_symbol_type(callee_id, field_ty.clone());
            let param_capabilities = match &field_ty {
                Ty::Func(params, _) => func_param_capabilities(params),
                _ => self.callable_capabilities_for(callee_id),
            };
            let applied = self.apply_callable_type(
                env,
                args,
                arg_wrappers,
                field_ty,
                Vec::new(),
                Vec::new(),
                param_capabilities,
                0,
                receiver.span,
                dict_args,
                pending_dict_args,
            )?;
            self.record_symbol_type(callee_id, applied.call_ty);
            if applied.fresh_return && call_expr_id != NO_NODE_ID {
                self.metadata.mark_fresh_place(call_expr_id);
            }
            return Ok(applied.ret_ty);
        }

        if matches!(receiver_ty, Ty::Var(_)) {
            // Unconstrained receiver: default to row-polymorphic record field access.
            // If the caller wants method dispatch on a specific type (Map, ['a], …),
            // they must annotate the parameter; annotation drives type resolution.
            let field_ty = Ty::Var(self.fresh_var());
            let tail_ty = Ty::Var(self.fresh_var());
            unify(
                &mut self.subst,
                receiver_ty,
                Ty::Record(Row {
                    fields: vec![(method_name.to_string(), field_ty.clone())],
                    tail: Box::new(tail_ty),
                }),
            )?;
            let applied = self.apply_callable_type(
                env,
                args,
                arg_wrappers,
                field_ty,
                Vec::new(),
                Vec::new(),
                Vec::new(),
                0,
                receiver.span,
                dict_args,
                pending_dict_args,
            )?;
            self.record_symbol_type(callee_id, applied.call_ty);
            return Ok(applied.ret_ty);
        }

        for target_name in inherent_impl_target_keys_from_ty(&receiver_ty) {
            let method_info = self
                .inherent_methods
                .get(&target_name)
                .and_then(|methods| methods.get(method_name))
                .or_else(|| {
                    self.scoped_inherent_methods
                        .get(&target_name)
                        .and_then(|methods| methods.get(method_name))
                })
                .cloned();
            let Some(method_info) = method_info else {
                continue;
            };
            let method_ty = self.instantiate_value(&method_info.scheme);
            self.record_symbol_type(callee_id, method_ty);
            if !method_info.has_receiver {
                return Err(TypeError::AssociatedFunctionAsMethod {
                    target: target_name,
                    function: method_name.to_string(),
                }
                .into());
            }
            if scheme_param_capability(&method_info.scheme, 0).is_mut_place() {
                self.check_mutable_place_arg(env, receiver, 0)?;
            }
            let applied = self.apply_scheme_callable(
                env,
                args,
                arg_wrappers,
                &method_info.scheme,
                vec![receiver_ty],
                1,
                dict_args,
                pending_dict_args,
            )?;
            self.record_symbol_type(
                callee_id,
                Ty::Func(
                    value_func_params(applied.arg_tys),
                    value_func_return(applied.ret_ty.clone()),
                ),
            );
            *is_method_call = true;
            *resolved_callee = Some(method_info.resolved_callee);
            return Ok(applied.ret_ty);
        }

        if let Some(info) = env.get(method_name) {
            let scheme = info.scheme.clone();
            let method_ty = self.instantiate_value(&scheme);
            self.record_symbol_type(callee_id, method_ty);
            if scheme_param_capability(&scheme, 0).is_mut_place() {
                self.check_mutable_place_arg(env, receiver, 0)?;
            }
            let applied = self.apply_scheme_callable(
                env,
                args,
                arg_wrappers,
                &scheme,
                vec![receiver_ty],
                1,
                dict_args,
                pending_dict_args,
            )?;
            self.record_symbol_type(
                callee_id,
                Ty::Func(
                    value_func_params(applied.arg_tys),
                    value_func_return(applied.ret_ty.clone()),
                ),
            );
            *is_method_call = true;
            *resolved_callee = Some(ResolvedCallee::Function(method_name.to_string()));
            return Ok(applied.ret_ty);
        }

        if let Some(expected_ret) = expected_ret
            && args.is_empty()
            && is_array_with_unresolved_element(&receiver_ty)
            && let Some((target_name, method_info, expected_receiver_ty)) =
                self.array_method_matching_expected_return(method_name, &expected_ret)
        {
            unify(
                &mut self.subst,
                receiver_ty.clone(),
                expected_receiver_ty.clone(),
            )?;
            let method_ty = self.instantiate_value(&method_info.scheme);
            self.record_symbol_type(callee_id, method_ty);
            if !method_info.has_receiver {
                return Err(TypeError::AssociatedFunctionAsMethod {
                    target: target_name,
                    function: method_name.to_string(),
                }
                .into());
            }
            if scheme_param_capability(&method_info.scheme, 0).is_mut_place() {
                self.check_mutable_place_arg(env, receiver, 0)?;
            }
            let applied = self.apply_scheme_callable(
                env,
                args,
                arg_wrappers,
                &method_info.scheme,
                vec![expected_receiver_ty],
                1,
                dict_args,
                pending_dict_args,
            )?;
            unify(&mut self.subst, applied.ret_ty.clone(), expected_ret)?;
            self.record_symbol_type(
                callee_id,
                Ty::Func(
                    value_func_params(applied.arg_tys),
                    value_func_return(applied.ret_ty.clone()),
                ),
            );
            *is_method_call = true;
            *resolved_callee = Some(method_info.resolved_callee);
            return Ok(applied.ret_ty);
        }

        let receiver = pretty_method_receiver_for_error(&receiver_ty);
        let candidates = self.inherent_method_candidates(method_name);
        if candidates.is_empty() {
            Err(TypeError::UnknownMethod {
                receiver,
                method: method_name.to_string(),
            }
            .into())
        } else if is_array_with_unresolved_element(&receiver_ty)
            && candidates
                .iter()
                .any(|candidate| candidate.starts_with('['))
        {
            Err(TypeError::UnknownMethodOnUnresolvedArray {
                receiver,
                method: method_name.to_string(),
                candidates,
            }
            .into())
        } else {
            Err(TypeError::UnknownMethodWithCandidates {
                receiver,
                method: method_name.to_string(),
                candidates,
            }
            .into())
        }
    }

    fn inherent_method_candidates(&self, method_name: &str) -> Vec<String> {
        let mut seen = HashSet::new();
        let mut candidates = Vec::new();
        for methods_by_target in [&self.inherent_methods, &self.scoped_inherent_methods] {
            for (target, methods) in methods_by_target {
                let Some(info) = methods.get(method_name) else {
                    continue;
                };
                if !info.has_receiver {
                    continue;
                }
                let candidate = format!(
                    "{}.{}",
                    format_inherent_target_for_error(target),
                    method_name
                );
                if seen.insert(candidate.clone()) {
                    candidates.push(candidate);
                }
            }
        }
        candidates.sort();
        candidates
    }

    fn array_method_matching_expected_return(
        &mut self,
        method_name: &str,
        expected_ret: &Ty,
    ) -> Option<(String, InherentMethodInfo, Ty)> {
        let mut candidates = Vec::new();
        let mut seen = HashSet::new();
        for methods_by_target in [&self.inherent_methods, &self.scoped_inherent_methods] {
            for (target, methods) in methods_by_target {
                let Some(receiver_ty) = array_receiver_ty_from_target_key(target) else {
                    continue;
                };
                let Some(method_info) = methods.get(method_name) else {
                    continue;
                };
                if !seen.insert(target.clone()) {
                    continue;
                }
                if !method_info.has_receiver {
                    continue;
                }
                candidates.push((target.clone(), method_info.clone(), receiver_ty));
            }
        }

        let mut matches = Vec::new();
        for (target, method_info, receiver_ty) in candidates {
            let Some(method_ret) = scheme_return_ty(&method_info.scheme) else {
                continue;
            };
            let snapshot = self.subst.snapshot_map();
            let matched = unify(&mut self.subst, method_ret, expected_ret.clone()).is_ok();
            self.subst.restore_map(snapshot);
            if matched {
                matches.push((target, method_info, receiver_ty));
            }
        }
        (matches.len() == 1).then(|| matches.remove(0))
    }

    pub(super) fn bare_trait_method(
        &self,
        method_name: &str,
    ) -> Result<Option<ResolvedTraitMethod>, TypeError> {
        let mut matching: Vec<_> = self
            .trait_env
            .values()
            .filter_map(|trait_def| {
                trait_def
                    .methods
                    .iter()
                    .find(|method| method.name == method_name)
                    .map(|method| ResolvedTraitMethod {
                        trait_def: trait_def.clone(),
                        method: method.clone(),
                    })
            })
            .collect();
        matching.sort_by(|a, b| a.trait_def.name.cmp(&b.trait_def.name));

        if matching.len() > 1 {
            return Err(TypeError::AmbiguousTraitMethod {
                method: method_name.to_string(),
                candidates: matching
                    .iter()
                    .map(|candidate| candidate.trait_def.name.clone())
                    .collect(),
            });
        }

        Ok(matching.into_iter().next())
    }

    pub(super) fn infer_args(
        &mut self,
        env: &TypeEnv,
        args: &mut [Expr],
        arg_wrappers: &mut Vec<Option<ArgWrapper>>,
    ) -> Result<Vec<Ty>, SpannedTypeError> {
        arg_wrappers.clear();
        let mut arg_tys = Vec::with_capacity(args.len());
        for arg in args {
            let inferred = self.infer_expr(env, arg)?;
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
            let mut arg_ty = self.subst.apply(&inferred);
            let wrapper = if let Ty::Qualified(constraints, inner) = arg_ty {
                let mut wrapper = ArgWrapper {
                    dict_args: Vec::new(),
                    pending_dict_args: Vec::new(),
                };
                attach_dict_args(
                    env,
                    &self.known_impl_dicts,
                    &self.known_impl_schemes,
                    &mut wrapper.dict_args,
                    &mut wrapper.pending_dict_args,
                    &mut self.pending_constraints,
                    &constraints,
                    &self.subst,
                )
                .map_err(|e| e.at(arg.span))?;
                arg_ty = *inner;
                Some(wrapper)
            } else {
                None
            };
            arg_wrappers.push(wrapper);
            arg_tys.push(arg_ty);
        }
        Ok(arg_tys)
    }

    pub(super) fn infer_checked_args(
        &mut self,
        env: &TypeEnv,
        args: &mut [Expr],
        arg_wrappers: &mut Vec<Option<ArgWrapper>>,
        param_capabilities: &[ParamCapability],
        param_offset: usize,
    ) -> Result<Vec<Ty>, SpannedTypeError> {
        let arg_tys = self.infer_args(env, args, arg_wrappers)?;
        self.check_mutable_place_args_from(env, args, param_capabilities, param_offset)?;
        Ok(arg_tys)
    }

    #[allow(clippy::too_many_arguments)]
    pub(super) fn apply_scheme_callable(
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
        let mut arg_tys = leading_arg_tys;
        arg_tys.extend(self.infer_checked_args(
            env,
            args,
            arg_wrappers,
            &scheme_param_capabilities(scheme),
            param_offset,
        )?);
        let ret_ty = self.infer_constrained_apply(
            env,
            scheme,
            arg_tys.clone(),
            dict_args,
            pending_dict_args,
        )?;
        Ok(AppliedSchemeCall {
            ret_ty,
            arg_tys,
            fresh_return: scheme_return_capability(scheme) == ReturnCapability::FreshPlace,
        })
    }

    #[allow(clippy::too_many_arguments)]
    pub(super) fn apply_callable_type(
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
        let mut arg_tys = leading_arg_tys;
        arg_tys.extend(self.infer_checked_args(
            env,
            args,
            arg_wrappers,
            &param_capabilities,
            param_offset,
        )?);
        let ret_ty = Ty::Var(self.fresh_var());
        let call_ty = Ty::Func(
            expected_func_params(&callable_ty, arg_tys.clone()),
            expected_func_return(&callable_ty, ret_ty.clone()),
        );
        unify(&mut self.subst, callable_ty, call_ty.clone())?;
        attach_dict_args(
            env,
            &self.known_impl_dicts,
            &self.known_impl_schemes,
            dict_args,
            pending_dict_args,
            &mut self.pending_constraints,
            &constraints,
            &self.subst,
        )
        .map_err(|err| err.at(dict_error_span))?;
        Ok(AppliedCall {
            ret_ty: self.subst.apply(&ret_ty),
            call_ty,
            fresh_return,
        })
    }

    pub(super) fn infer_constrained_apply(
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
            &self.known_impl_dicts,
            &self.known_impl_schemes,
            dict_args,
            pending_dict_args,
            &mut self.pending_constraints,
            &instantiated.constraints,
            &self.subst,
        )
        .map_err(TypeError::unspanned)?;
        Ok(self.subst.apply(&ret_ty))
    }
}

fn format_inherent_target_for_error(target: &str) -> String {
    if target == "Array" {
        return "['a]".to_string();
    }
    if let Some(element) = target.strip_prefix("Array__app1__") {
        return format!("[{}]", format_inherent_target_for_error(element));
    }
    target.to_string()
}

fn array_receiver_ty_from_target_key(target: &str) -> Option<Ty> {
    let element = target.strip_prefix("Array__app1__")?;
    let element_ty = match element {
        "int" => Ty::Int,
        "float" => Ty::Float,
        "string" => Ty::Con("string".to_string()),
        "bool" => Ty::Con("bool".to_string()),
        _ => return None,
    };
    Some(Ty::App(
        Box::new(Ty::Con("Array".to_string())),
        vec![element_ty],
    ))
}

fn scheme_return_ty(scheme: &Scheme) -> Option<Ty> {
    match &scheme.ty {
        Ty::Func(_, ret) => Some((*ret.ty).clone()),
        _ => None,
    }
}

fn pretty_method_receiver_for_error(receiver: &Ty) -> String {
    let names: HashMap<_, _> = free_type_vars_in_display_order(receiver)
        .into_iter()
        .enumerate()
        .map(|(index, var)| (var, type_var_name(index)))
        .collect();
    display_ty_with_var_names(receiver, &names)
}

fn is_array_with_unresolved_element(receiver: &Ty) -> bool {
    matches!(
        receiver,
        Ty::App(con, args)
            if matches!(con.as_ref(), Ty::Con(name) if name == "Array")
                && matches!(args.as_slice(), [Ty::Var(_)])
    )
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
