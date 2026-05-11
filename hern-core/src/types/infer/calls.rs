use super::*;

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
                    method: mangle_op(op),
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
        let Some(target_name) = ty_target_name(&target) else {
            return Err(TypeError::MissingTraitImpl {
                trait_name: trait_name.to_string(),
                impl_target: format!("{}", target),
            });
        };
        if !has_trait_impl(env, &self.known_impl_dicts, trait_name, &target_name) {
            return Err(TypeError::MissingTraitImpl {
                trait_name: trait_name.to_string(),
                impl_target: target_name,
            });
        }
        Ok(DictResolution::Resolved(DictRef::Concrete(format!(
            "__{}__{}",
            trait_name, target_name
        ))))
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
                let Some(target_name) = ty_target_name(&resolved) else {
                    return Err(TypeError::MissingTraitImpl {
                        trait_name: "Eq".to_string(),
                        impl_target: format!("{}", resolved),
                    }
                    .into());
                };
                if !has_trait_impl(env, &self.known_impl_dicts, "Eq", &target_name) {
                    return Err(TypeError::MissingTraitImpl {
                        trait_name: "Eq".to_string(),
                        impl_target: target_name,
                    }
                    .into());
                }
                Ok(DictRef::Concrete(format!("__Eq__{}", target_name)))
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
            let target_name =
                ty_target_name(&resolved_target).ok_or_else(|| TypeError::UnresolvedTrait {
                    context: context.to_string(),
                    trait_name: trait_name.clone(),
                })?;
            let dict_name = format!("__{}__{}", trait_name, target_name);

            let ret_ty = if let Some(dict_info) = env.get(&dict_name) {
                let dict_ty = self.instantiate(&dict_info.scheme);
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
            } else if self.known_impl_dicts.contains(&dict_name) {
                self.check_trait_method_signature(&trait_def, &method, arg_tys, context)?
            } else {
                return Err(TypeError::MissingTraitImpl {
                    trait_name: trait_name.clone(),
                    impl_target: target_name.to_string(),
                }
                .into());
            };

            *resolved_callee = Some(ResolvedCallee::DictMethod {
                dict: DictRef::Concrete(format!("__{}__{}", trait_name, target_name)),
                method: mangle_op(&method_name),
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
            match ty_target_name(&resolved_target) {
                None => {
                    if let Ty::Var(v) = resolved_target {
                        *pending_trait_method = Some((
                            PendingDictArg {
                                var: v,
                                trait_name: trait_name.clone(),
                            },
                            method_name,
                        ));
                    }
                    Ok(self.subst.apply(&ret_ty))
                }
                Some(target_name) => {
                    let dict_name = format!("__{}__{}", trait_name, target_name);
                    if env.get(&dict_name).is_none() && !self.known_impl_dicts.contains(&dict_name)
                    {
                        return Err(TypeError::MissingTraitImpl {
                            trait_name: trait_name.clone(),
                            impl_target: target_name.to_string(),
                        }
                        .into());
                    }
                    *resolved_callee = Some(ResolvedCallee::DictMethod {
                        dict: DictRef::Concrete(format!("__{}__{}", trait_name, target_name)),
                        method: mangle_op(&method_name),
                    });
                    Ok(self.subst.apply(&ret_ty))
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
        ty_target_name(&resolved_target).ok_or_else(|| TypeError::UnresolvedTrait {
            context: context.to_string(),
            trait_name: trait_def.name.clone(),
        })?;
        Ok(ret_ty)
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
        let target_name = validate_inherent_impl_target(target, &self.declared_types)
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

        self.check_mutable_place_args(env, args, &scheme_param_capabilities(&method_info.scheme))?;
        let arg_tys = self.infer_args(env, args, arg_wrappers)?;
        let return_capability = scheme_return_capability(&method_info.scheme);
        let fresh_return = return_capability == ReturnCapability::FreshPlace;
        let ret_ty = self.infer_constrained_apply(
            env,
            &method_info.scheme,
            arg_tys.clone(),
            dict_args,
            pending_dict_args,
        )?;
        self.record_symbol_type(
            callee_id,
            Ty::Func(
                expected_func_params(&method_ty, arg_tys),
                FuncReturn {
                    ty: Box::new(ret_ty.clone()),
                    capability: return_capability,
                },
            ),
        );
        *resolved_callee = Some(method_info.resolved_callee);
        if fresh_return && call_expr_id != NO_NODE_ID {
            self.fresh_place_exprs.insert(call_expr_id);
        }
        Ok(ret_ty)
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
            let fresh_return = func_return_capability(&field_ty) == ReturnCapability::FreshPlace;
            let param_capabilities = match &field_ty {
                Ty::Func(params, _) => func_param_capabilities(params),
                _ => self.callable_capabilities_for(callee_id),
            };
            self.check_mutable_place_args(env, args, &param_capabilities)?;
            let arg_tys = self.infer_args(env, args, arg_wrappers)?;
            let ret_ty = Ty::Var(self.fresh_var());
            let call_ty = Ty::Func(
                expected_func_params(&field_ty, arg_tys),
                expected_func_return(&field_ty, ret_ty.clone()),
            );
            unify(&mut self.subst, field_ty, call_ty.clone())?;
            self.record_symbol_type(callee_id, call_ty);
            if fresh_return && call_expr_id != NO_NODE_ID {
                self.fresh_place_exprs.insert(call_expr_id);
            }
            return Ok(self.subst.apply(&ret_ty));
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
            let arg_tys = self.infer_args(env, args, arg_wrappers)?;
            let ret_ty = Ty::Var(self.fresh_var());
            let call_ty = Ty::Func(
                value_func_params(arg_tys),
                value_func_return(ret_ty.clone()),
            );
            unify(&mut self.subst, field_ty, call_ty.clone())?;
            self.record_symbol_type(callee_id, call_ty);
            return Ok(self.subst.apply(&ret_ty));
        }

        let target_name = ty_target_name(&receiver_ty).unwrap_or_else(|| receiver_ty.to_string());

        if let Some(method_info) = self
            .inherent_methods
            .get(&target_name)
            .and_then(|methods| methods.get(method_name))
            .cloned()
        {
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
            let param_capabilities = scheme_param_capabilities(&method_info.scheme);
            self.check_mutable_place_args_from(env, args, &param_capabilities, 1)?;
            let mut arg_tys = Vec::with_capacity(args.len() + 1);
            arg_tys.push(receiver_ty);
            arg_tys.extend(self.infer_args(env, args, arg_wrappers)?);
            let ret_ty = self.infer_constrained_apply(
                env,
                &method_info.scheme,
                arg_tys.clone(),
                dict_args,
                pending_dict_args,
            )?;
            self.record_symbol_type(
                callee_id,
                Ty::Func(
                    value_func_params(arg_tys),
                    value_func_return(ret_ty.clone()),
                ),
            );
            *is_method_call = true;
            *resolved_callee = Some(method_info.resolved_callee);
            return Ok(ret_ty);
        }

        if let Some(method_info) = self
            .scoped_inherent_methods
            .get(&target_name)
            .and_then(|methods| methods.get(method_name))
            .cloned()
        {
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
            let param_capabilities = scheme_param_capabilities(&method_info.scheme);
            self.check_mutable_place_args_from(env, args, &param_capabilities, 1)?;
            let mut arg_tys = Vec::with_capacity(args.len() + 1);
            arg_tys.push(receiver_ty);
            arg_tys.extend(self.infer_args(env, args, arg_wrappers)?);
            let ret_ty = self.infer_constrained_apply(
                env,
                &method_info.scheme,
                arg_tys.clone(),
                dict_args,
                pending_dict_args,
            )?;
            self.record_symbol_type(
                callee_id,
                Ty::Func(
                    value_func_params(arg_tys),
                    value_func_return(ret_ty.clone()),
                ),
            );
            *is_method_call = true;
            *resolved_callee = Some(method_info.resolved_callee);
            return Ok(ret_ty);
        }

        if let Some(info) = env.get(method_name) {
            let scheme = info.scheme.clone();
            let method_ty = self.instantiate_value(&scheme);
            self.record_symbol_type(callee_id, method_ty);
            if scheme_param_capability(&scheme, 0).is_mut_place() {
                self.check_mutable_place_arg(env, receiver, 0)?;
            }
            self.check_mutable_place_args_from(env, args, &scheme_param_capabilities(&scheme), 1)?;
            let mut arg_tys = Vec::with_capacity(args.len() + 1);
            arg_tys.push(receiver_ty);
            arg_tys.extend(self.infer_args(env, args, arg_wrappers)?);
            let ret_ty = self.infer_constrained_apply(
                env,
                &scheme,
                arg_tys.clone(),
                dict_args,
                pending_dict_args,
            )?;
            self.record_symbol_type(
                callee_id,
                Ty::Func(
                    value_func_params(arg_tys),
                    value_func_return(ret_ty.clone()),
                ),
            );
            *is_method_call = true;
            *resolved_callee = Some(ResolvedCallee::Function(method_name.to_string()));
            return Ok(ret_ty);
        }

        Err(TypeError::UnknownMethod {
            receiver: target_name,
            method: method_name.to_string(),
        }
        .into())
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
                    .callable_capabilities
                    .get(&arg.id)
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
