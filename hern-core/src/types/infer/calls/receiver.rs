//! Receiver-method resolution for dot calls.
//!
//! Receiver calls try inherent methods first, then trait methods, while preserving
//! useful ambiguity and missing-method diagnostics for editor recovery.

use super::*;

impl Infer {
    #[allow(clippy::too_many_arguments)]
    pub(in crate::types::infer) fn resolve_receiver_call(
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
        let imported_member_scheme = self.imported_member_scheme(receiver, method_name);
        if let Some(scheme) = &imported_member_scheme {
            if matches!(scheme.ty, Ty::Func(_, _)) {
                self.record_callable_capabilities(callee_id, scheme_param_capabilities(scheme));
            }
        } else if let ExprKind::Ident(base_name) = &receiver.kind
            && let Some(param_capabilities) = self
                .inherent
                .record_field_callables
                .get(base_name)
                .and_then(|fields| fields.get(method_name))
                .cloned()
        {
            self.record_callable_capabilities(callee_id, param_capabilities);
        }

        if let Some(scheme) = imported_member_scheme {
            let instantiated = self.instantiate_scheme(&scheme);
            let mut field_ty = instantiated.ty;
            let mut constraints = instantiated.constraints;
            if let Ty::Qualified(existing, inner) = field_ty {
                constraints.extend(existing);
                field_ty = *inner;
            }
            if !constraints.is_empty() {
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
                .map_err(|e| e.at(receiver.span))?;
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
                None,
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

        if let Some(mut field_ty) = record_field_ty(&receiver_ty, method_name) {
            if let Ty::Qualified(constraints, inner) = field_ty {
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
                None,
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
                None,
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
                .inherent
                .methods
                .get(&target_name)
                .and_then(|methods| methods.get(method_name))
                .or_else(|| {
                    self.inherent
                        .scoped_methods
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
                Some(receiver.span),
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

        if let Some(ret_ty) = self.resolve_receiver_trait_call(
            env,
            callee_id,
            &receiver_ty,
            method_name,
            args,
            arg_wrappers,
            is_method_call,
            resolved_callee,
        )? {
            return Ok(ret_ty);
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
                Some(receiver.span),
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
                Some(receiver.span),
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
        for methods_by_target in [&self.inherent.methods, &self.inherent.scoped_methods] {
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

    #[allow(clippy::too_many_arguments)]
    fn resolve_receiver_trait_call(
        &mut self,
        env: &TypeEnv,
        callee_id: NodeId,
        receiver_ty: &Ty,
        method_name: &str,
        args: &mut [Expr],
        arg_wrappers: &mut Vec<Option<ArgWrapper>>,
        is_method_call: &mut bool,
        resolved_callee: &mut Option<ResolvedCallee>,
    ) -> Result<Option<Ty>, SpannedTypeError> {
        let candidates = self.receiver_trait_method_candidates(method_name);
        if candidates.is_empty() {
            return Ok(None);
        }

        let mut matches = Vec::new();
        let mut receiver_matches = Vec::new();
        for candidate in &candidates {
            let snapshot = self.subst.checkpoint();
            let mut probe_args = args.to_vec();
            let mut probe_arg_wrappers = Vec::new();
            let matched = self
                .infer_args(env, &mut probe_args, &mut probe_arg_wrappers)
                .and_then(|arg_tys| {
                    self.try_receiver_trait_method(env, receiver_ty, &arg_tys, candidate)
                })
                .is_ok();
            self.subst.restore_checkpoint(snapshot);
            if matched {
                matches.push(candidate.clone());
                receiver_matches.push(candidate.clone());
                continue;
            }

            let snapshot = self.subst.checkpoint();
            let receiver_matched =
                self.receiver_trait_method_matches_receiver(env, receiver_ty, candidate);
            self.subst.restore_checkpoint(snapshot);
            if receiver_matched {
                receiver_matches.push(candidate.clone());
            }
        }

        if matches.len() > 1 {
            return Err(TypeError::AmbiguousTraitMethod {
                method: method_name.to_string(),
                candidates: matches
                    .iter()
                    .map(|candidate| candidate.trait_def.name.clone())
                    .collect(),
            }
            .into());
        }

        let Some(candidate) = matches.into_iter().next() else {
            if receiver_matches.len() == 1 {
                let candidate = receiver_matches
                    .into_iter()
                    .next()
                    .expect("single receiver match exists");
                if candidate.method.params.len() != args.len() + 1 {
                    return Err(TypeError::ArityMismatch {
                        expected: candidate.method.params.len().saturating_sub(1),
                        got: args.len(),
                    }
                    .into());
                }
                let arg_tys = self.infer_args(env, args, arg_wrappers)?;
                let resolved =
                    self.try_receiver_trait_method(env, receiver_ty, &arg_tys, &candidate)?;
                self.record_symbol_type(
                    callee_id,
                    Ty::Func(
                        value_func_params(arg_tys),
                        value_func_return(resolved.ret_ty.clone()),
                    ),
                );
                *is_method_call = true;
                *resolved_callee = Some(resolved.resolved_callee);
                return Ok(Some(resolved.ret_ty));
            }
            return Ok(None);
        };

        let arg_tys = self.infer_args(env, args, arg_wrappers)?;
        let resolved = self.try_receiver_trait_method(env, receiver_ty, &arg_tys, &candidate)?;
        self.record_symbol_type(
            callee_id,
            Ty::Func(
                value_func_params(arg_tys),
                value_func_return(resolved.ret_ty.clone()),
            ),
        );
        *is_method_call = true;
        *resolved_callee = Some(resolved.resolved_callee);
        Ok(Some(resolved.ret_ty))
    }

    fn receiver_trait_method_candidates(&self, method_name: &str) -> Vec<ReceiverTraitMethodMatch> {
        let mut candidates = self
            .traits
            .env
            .values()
            .filter_map(|trait_def| {
                trait_def
                    .methods
                    .iter()
                    .find(|method| method.name == method_name)
                    .map(|method| ReceiverTraitMethodMatch {
                        trait_def: trait_def.clone(),
                        method: method.clone(),
                    })
            })
            .collect::<Vec<_>>();
        candidates.sort_by(|left, right| left.trait_def.name.cmp(&right.trait_def.name));
        candidates
    }

    fn try_receiver_trait_method(
        &mut self,
        env: &TypeEnv,
        receiver_ty: &Ty,
        arg_tys: &[Ty],
        candidate: &ReceiverTraitMethodMatch,
    ) -> Result<ReceiverTraitMethodResolution, SpannedTypeError> {
        let trait_def = &candidate.trait_def;
        let method = &candidate.method;
        if method.params.len() != arg_tys.len() + 1 {
            return Err(TypeError::ArityMismatch {
                expected: method.params.len().saturating_sub(1),
                got: arg_tys.len(),
            }
            .into());
        }

        let mut param_vars = HashMap::new();
        let trait_vars = trait_def
            .params
            .iter()
            .map(|param| {
                let var = self.fresh_var();
                param_vars.insert(param.clone(), var);
                var
            })
            .collect::<Vec<_>>();
        let method_param_tys = method
            .params
            .iter()
            .map(|(_, ty)| self.ast_to_ty_with_vars(ty, &mut param_vars))
            .collect::<Result<Vec<_>, _>>()?;
        let ret_ty = self.ast_to_ty_with_vars(&method.ret_type, &mut param_vars)?;

        unify(
            &mut self.subst,
            method_param_tys[0].clone(),
            receiver_ty.clone(),
        )?;
        for (actual, expected) in arg_tys
            .iter()
            .cloned()
            .zip(method_param_tys.into_iter().skip(1))
        {
            unify(&mut self.subst, actual, expected)?;
        }

        let trait_args = trait_vars
            .into_iter()
            .map(|var| self.subst.apply(&Ty::Var(var)))
            .collect::<Vec<_>>();
        let determinant_indexes = trait_dict_indexes(trait_def);
        let dict = resolve_concrete_from_args_unifying(
            &trait_def.name,
            &trait_args,
            &determinant_indexes,
            env,
            &self.impls.active_dicts,
            &self.impls.known_schemes,
            &mut self.subst,
        )
        .map_err(SpannedTypeError::from)?
        .ok_or_else(|| TypeError::MissingTraitImpl {
            trait_name: trait_def.name.clone(),
            impl_target: format_trait_target_for_receiver_error(&trait_args, &determinant_indexes),
        })?;

        let dict_name = dict_ref_concrete_name(&dict)
            .expect("receiver trait method dictionaries should be concrete")
            .to_string();
        if let Some(dict_scheme) = env
            .get(&dict_name)
            .map(|info| info.scheme.clone())
            .or_else(|| self.impls.known_schemes.get(&dict_name).cloned())
        {
            let dict_ty = self.instantiate(&dict_scheme);
            let method_ty =
                record_field_ty(&self.subst.apply(&dict_ty), &method.name).ok_or_else(|| {
                    TypeError::UnknownTraitMethod {
                        trait_name: trait_def.name.clone(),
                        method: method.name.clone(),
                    }
                })?;
            let checked_ret = Ty::Var(self.fresh_var());
            let mut all_args = Vec::with_capacity(arg_tys.len() + 1);
            all_args.push(receiver_ty.clone());
            all_args.extend(arg_tys.iter().cloned());
            unify(
                &mut self.subst,
                method_ty,
                Ty::Func(
                    value_func_params(all_args),
                    value_func_return(checked_ret.clone()),
                ),
            )?;
            unify(&mut self.subst, ret_ty.clone(), checked_ret)?;
        }

        Ok(ReceiverTraitMethodResolution {
            ret_ty: self.subst.apply(&ret_ty),
            resolved_callee: ResolvedCallee::DictMethod {
                dict,
                method: method.name.clone(),
            },
        })
    }

    fn receiver_trait_method_matches_receiver(
        &mut self,
        env: &TypeEnv,
        receiver_ty: &Ty,
        candidate: &ReceiverTraitMethodMatch,
    ) -> bool {
        let trait_def = &candidate.trait_def;
        let method = &candidate.method;
        let Some((_, receiver_ast_ty)) = method.params.first() else {
            return false;
        };

        let mut param_vars = HashMap::new();
        let trait_vars = trait_def
            .params
            .iter()
            .map(|param| {
                let var = self.fresh_var();
                param_vars.insert(param.clone(), var);
                var
            })
            .collect::<Vec<_>>();
        let Ok(expected_receiver_ty) = self.ast_to_ty_with_vars(receiver_ast_ty, &mut param_vars)
        else {
            return false;
        };
        if unify(&mut self.subst, expected_receiver_ty, receiver_ty.clone()).is_err() {
            return false;
        }

        let trait_args = trait_vars
            .into_iter()
            .map(|var| self.subst.apply(&Ty::Var(var)))
            .collect::<Vec<_>>();
        let determinant_indexes = trait_dict_indexes(trait_def);
        resolve_concrete_from_args_unifying(
            &trait_def.name,
            &trait_args,
            &determinant_indexes,
            env,
            &self.impls.active_dicts,
            &self.impls.known_schemes,
            &mut self.subst,
        )
        .ok()
        .flatten()
        .is_some()
    }

    fn array_method_matching_expected_return(
        &mut self,
        method_name: &str,
        expected_ret: &Ty,
    ) -> Option<(String, InherentMethodInfo, Ty)> {
        let mut candidates = Vec::new();
        let mut seen = HashSet::new();
        for methods_by_target in [&self.inherent.methods, &self.inherent.scoped_methods] {
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
            let snapshot = self.subst.checkpoint();
            let matched = unify(&mut self.subst, method_ret, expected_ret.clone()).is_ok();
            self.subst.restore_checkpoint(snapshot);
            if matched {
                matches.push((target, method_info, receiver_ty));
            }
        }
        (matches.len() == 1).then(|| matches.remove(0))
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

fn format_trait_target_for_receiver_error(args: &[Ty], determinant_indexes: &[usize]) -> String {
    let target = determinant_indexes
        .first()
        .and_then(|index| args.get(*index))
        .or_else(|| args.first());
    target
        .map(pretty_method_receiver_for_error)
        .unwrap_or_else(|| "<unknown>".to_string())
}

fn is_array_with_unresolved_element(receiver: &Ty) -> bool {
    matches!(
        receiver,
        Ty::App(con, args)
            if matches!(con.as_ref(), Ty::Con(name) if name == "Array")
                && matches!(args.as_slice(), [Ty::Var(_)])
    )
}
