use super::*;

impl Infer {
    pub(super) fn export_inherent_method_schemes(
        &self,
    ) -> HashMap<String, HashMap<String, InherentMethodScheme>> {
        self.inherent_methods
            .iter()
            .map(|(target, methods)| {
                (
                    target.clone(),
                    methods
                        .iter()
                        .map(|(name, info)| {
                            (
                                name.clone(),
                                InherentMethodScheme {
                                    scheme: self.subst.apply_scheme(&info.scheme),
                                    has_receiver: info.has_receiver,
                                },
                            )
                        })
                        .collect(),
                )
            })
            .collect()
    }

    pub(super) fn infer_impl(
        &mut self,
        env: &mut TypeEnv,
        id: &mut ImplDef,
    ) -> Result<(), SpannedTypeError> {
        let trait_def = self
            .trait_env
            .get(&id.trait_name)
            .ok_or_else(|| TypeError::UnknownTrait(id.trait_name.clone()))?
            .clone();

        let impl_target =
            trait_impl_target_key_from_ast(&id.target).map_err(|err| err.at(id.span))?;
        if trait_uses_param_as_constructor(&trait_def)
            && matches!(id.target, Type::App(_, _))
            && !type_has_hole(&id.target)
        {
            return Err(
                TypeError::InvalidTraitImplTarget(type_name_for_error_ast(&id.target)).at(id.span),
            );
        }

        for tm in &trait_def.methods {
            if !id.methods.iter().any(|m| m.name == tm.name) {
                return Err(TypeError::MissingTraitMethod {
                    trait_name: id.trait_name.clone(),
                    impl_target: impl_target.clone(),
                    method: tm.name.clone(),
                }
                .into());
            }
        }

        let mut dict_fields: Vec<(String, Ty)> = Vec::new();
        let mut impl_param_vars = HashMap::new();
        let _impl_target_ty = self.ast_to_ty_with_vars(&id.target, &mut impl_param_vars)?;
        let initial_constraints =
            self.collect_type_bound_constraints(&mut impl_param_vars, &id.type_bounds);
        let saved_pending = std::mem::take(&mut self.pending_constraints);
        self.pending_constraints.extend(initial_constraints);

        for impl_method in &mut id.methods {
            let Some(trait_method) = trait_def
                .methods
                .iter()
                .find(|m| m.name == impl_method.name)
            else {
                return Err(TypeError::ExtraTraitMethod {
                    trait_name: id.trait_name.clone(),
                    method: impl_method.name.clone(),
                }
                .at(impl_method.span));
            };

            if trait_method.inline {
                impl_method.inline = true;
            }

            if impl_method.params.len() != trait_method.params.len() {
                return Err(TypeError::TraitMethodArityMismatch {
                    trait_name: id.trait_name.clone(),
                    method: impl_method.name.clone(),
                    expected: trait_method.params.len(),
                    got: impl_method.params.len(),
                }
                .at(impl_method.span));
            }

            let derived_params: Vec<Type> = trait_method
                .params
                .iter()
                .map(|(_, t)| subst_hkt_param(t, &trait_def.param, &id.target))
                .collect();
            let derived_ret = subst_hkt_param(&trait_method.ret_type, &trait_def.param, &id.target);

            let mut param_vars: HashMap<String, TyVar> = impl_param_vars.clone();
            let mut param_tys: Vec<Ty> = Vec::new();
            let mut body_env = env.clone();

            for (param, derived_ty) in impl_method.params.iter().zip(derived_params.iter()) {
                if param.mut_place {
                    return Err(TypeError::MutableFunctionCapabilityMismatch.at(impl_method.span));
                }
                if !is_irrefutable_param(&param.pat, &self.variant_env) {
                    return Err(TypeError::RefutableParamPattern.at(impl_method.body.span));
                }
                let p_ty = self.ast_to_ty_with_vars(derived_ty, &mut param_vars)?;
                if let Some(p_type) = &param.ty {
                    let explicit_ty = self.ast_to_ty_with_vars(p_type, &mut param_vars)?;
                    unify(&mut self.subst, p_ty.clone(), explicit_ty)
                        .map_err(|err| err.at(impl_method.body.span))?;
                }
                param_tys.push(p_ty.clone());
                self.check_pattern(&param.pat, p_ty, &mut body_env, false)?;
            }
            let ret_ty = self.ast_to_ty_with_vars(&derived_ret, &mut param_vars)?;

            if let Some(ret_type_opt) = &impl_method.ret_type {
                let explicit_ret = self.ast_to_ty_with_vars(&ret_type_opt.ty, &mut param_vars)?;
                unify(&mut self.subst, ret_ty.clone(), explicit_ret)
                    .map_err(|err| err.at(impl_method.body.span))?;
            }

            self.fn_return_tys.push(ret_ty.clone());
            let body_ty = self.infer_expr(&body_env, &mut impl_method.body)?;
            self.fn_return_tys.pop();
            unify_expr_result(&mut self.subst, body_ty, ret_ty.clone())
                .map_err(|err| err.at(impl_method.body.span))?;

            let method_ty = Ty::Func(value_func_params(param_tys), value_func_return(ret_ty));
            self.metadata
                .record_definition_scheme(impl_method.name_span, Scheme::mono(method_ty.clone()));
            dict_fields.push((impl_method.name.clone(), method_ty));
        }

        dict_fields.sort_by(|(a, _), (b, _)| a.cmp(b));
        let dict_ty = Ty::Record(Row {
            fields: dict_fields,
            tail: Box::new(Ty::Unit),
        });
        let fn_constraints = std::mem::replace(&mut self.pending_constraints, saved_pending);
        let finalized = self.finalize_constraints(env, dict_ty, fn_constraints);
        self.pending_constraints.extend(finalized.bubbled.clone());
        id.dict_params = finalized.owned.iter().map(dict_param_name).collect();
        let resolver = |p: &PendingDictArg| {
            resolve_local_or_concrete(
                p,
                &finalized.owned,
                env,
                &self.known_impl_dicts,
                &self.known_impl_schemes,
                &self.subst,
            )
        };
        for method in &mut id.methods {
            resolve_dict_uses_expr(&mut method.body, &resolver, false)?;
        }
        let dict_scheme = finalized.scheme;
        let dict_name = trait_impl_dict_name(&id.trait_name, &impl_target);
        env.insert(dict_name, EnvInfo::immutable(dict_scheme));
        Ok(())
    }

    pub(super) fn infer_inherent_impl(
        &mut self,
        env: &mut TypeEnv,
        id: &mut InherentImplDef,
    ) -> Result<(), SpannedTypeError> {
        let target_name = inherent_impl_target_key_from_ast(&id.target, &self.declared_types)
            .map_err(|err| err.at(id.span))?;
        let dict_name = inherent_impl_dict_name(&target_name);
        let mut seen_methods = HashSet::new();
        let mut dict_fields = Vec::new();

        for method in &mut id.methods {
            if !seen_methods.insert(method.name.clone())
                || self
                    .inherent_methods
                    .get(&target_name)
                    .is_some_and(|methods| methods.contains_key(&method.name))
            {
                return Err(TypeError::DuplicateInherentMethod {
                    target: target_name.clone(),
                    method: method.name.clone(),
                }
                .at(method.name_span));
            }
            let has_receiver = method.params.first().is_some_and(is_self_param);
            substitute_self_in_inherent_method(method, &id.target);

            let mut param_vars = HashMap::new();
            let target_ty = self.ast_to_ty_with_vars(&id.target, &mut param_vars)?;
            let initial_constraints =
                self.collect_type_bound_constraints(&mut param_vars, &method.type_bounds);
            let mut param_tys = Vec::new();
            let mut body_env = env.clone();

            for (idx, param) in method.params.iter().enumerate() {
                if !is_irrefutable_param(&param.pat, &self.variant_env) {
                    return Err(TypeError::RefutableParamPattern.at(method.body.span));
                }
                let p_ty = if has_receiver && idx == 0 {
                    let receiver_ty = target_ty.clone();
                    if let Some(explicit) = &param.ty {
                        let explicit_ty = self.ast_to_ty_with_vars(explicit, &mut param_vars)?;
                        unify(&mut self.subst, receiver_ty.clone(), explicit_ty)
                            .map_err(|err| err.at(method.body.span))?;
                    }
                    receiver_ty
                } else {
                    match &param.ty {
                        Some(t) => self.ast_to_ty_with_vars(t, &mut param_vars)?,
                        None => self.subst.fresh_var(),
                    }
                };
                param_tys.push(p_ty.clone());
                self.check_param_pattern(&param.pat, p_ty, &mut body_env, param.mut_place)?;
            }

            let ret_ty = match &method.ret_type {
                Some(t) => self.ast_to_ty_with_vars(&t.ty, &mut param_vars)?,
                None => self.subst.fresh_var(),
            };
            let fn_ty = Ty::Func(
                func_params_from_params(&method.params, param_tys.clone()),
                func_return_from_annotation(&method.ret_type, ret_ty.clone()),
            );

            let saved_pending = std::mem::take(&mut self.pending_constraints);
            self.pending_constraints.extend(initial_constraints);
            self.fn_return_tys.push(ret_ty.clone());
            let body_ty = self.infer_expr(&body_env, &mut method.body)?;
            self.fn_return_tys.pop();
            unify_expr_result(&mut self.subst, body_ty, ret_ty)
                .map_err(|err| err.at(method.body.span))?;

            let fn_constraints = std::mem::replace(&mut self.pending_constraints, saved_pending);
            let finalized = self.finalize_constraints(env, fn_ty.clone(), fn_constraints);
            self.pending_constraints.extend(finalized.bubbled.clone());
            method.dict_params = finalized.owned.iter().map(dict_param_name).collect();

            let resolver = |p: &PendingDictArg| {
                resolve_local_or_concrete(
                    p,
                    &finalized.owned,
                    env,
                    &self.known_impl_dicts,
                    &self.known_impl_schemes,
                    &self.subst,
                )
            };
            resolve_dict_uses_expr(&mut method.body, &resolver, false)?;

            let scheme = finalized.scheme.clone();
            self.metadata
                .record_definition_scheme(method.name_span, scheme.clone());
            self.inherent_methods
                .entry(target_name.clone())
                .or_default()
                .insert(
                    method.name.clone(),
                    InherentMethodInfo {
                        scheme,
                        resolved_callee: ResolvedCallee::InherentMethod {
                            dict: dict_name.clone(),
                            method: method.name.clone(),
                        },
                        has_receiver,
                    },
                );
            dict_fields.push((method.name.clone(), self.subst.apply(&fn_ty)));
        }

        dict_fields.sort_by(|(a, _), (b, _)| a.cmp(b));
        env.insert(
            dict_name,
            EnvInfo::immutable(self.generalize(
                env,
                Ty::Record(Row {
                    fields: dict_fields,
                    tail: Box::new(Ty::Unit),
                }),
            )),
        );
        Ok(())
    }
}

fn trait_uses_param_as_constructor(trait_def: &TraitDef) -> bool {
    trait_def.methods.iter().any(|method| {
        method
            .params
            .iter()
            .any(|(_, ty)| type_uses_var_as_constructor(ty, &trait_def.param))
            || type_uses_var_as_constructor(&method.ret_type, &trait_def.param)
    })
}

fn type_uses_var_as_constructor(ty: &Type, var_name: &str) -> bool {
    match ty {
        Type::App(con, args) => {
            matches!(con.as_ref(), Type::Var(name) if name == var_name)
                || type_uses_var_as_constructor(con, var_name)
                || args
                    .iter()
                    .any(|arg| type_uses_var_as_constructor(arg, var_name))
        }
        Type::Func(params, ret) => {
            params
                .iter()
                .any(|param| type_uses_var_as_constructor(&param.ty, var_name))
                || type_uses_var_as_constructor(&ret.ty, var_name)
        }
        Type::Tuple(items) => items
            .iter()
            .any(|item| type_uses_var_as_constructor(item, var_name)),
        Type::Record(fields, _) => fields
            .iter()
            .any(|(_, field_ty)| type_uses_var_as_constructor(field_ty, var_name)),
        Type::Ident(_) | Type::Var(_) | Type::Unit | Type::Never | Type::Hole => false,
    }
}

fn type_has_hole(ty: &Type) -> bool {
    match ty {
        Type::Hole => true,
        Type::App(con, args) => type_has_hole(con) || args.iter().any(type_has_hole),
        Type::Func(params, ret) => {
            params.iter().any(|param| type_has_hole(&param.ty)) || type_has_hole(&ret.ty)
        }
        Type::Tuple(items) => items.iter().any(type_has_hole),
        Type::Record(fields, _) => fields.iter().any(|(_, field_ty)| type_has_hole(field_ty)),
        Type::Ident(_) | Type::Var(_) | Type::Unit | Type::Never => false,
    }
}

fn type_name_for_error_ast(target: &Type) -> String {
    match target {
        Type::Ident(name) | Type::Var(name) => name.clone(),
        Type::App(con, args) => {
            let rendered_args = args
                .iter()
                .map(type_name_for_error_ast)
                .collect::<Vec<_>>()
                .join(", ");
            format!("{}({})", type_name_for_error_ast(con), rendered_args)
        }
        Type::Func(_, _) => "fn(...)".to_string(),
        Type::Tuple(_) => "(...)".to_string(),
        Type::Record(..) => "#{...}".to_string(),
        Type::Unit => "()".to_string(),
        Type::Never => "!".to_string(),
        Type::Hole => "*".to_string(),
    }
}
