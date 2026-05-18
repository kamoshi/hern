//! Trait and inherent implementation checking.
//!
//! Impl blocks validate that methods match their declared trait or inherent
//! surface, produce concrete dictionary schemes, and populate the known-impl
//! state used by later trait dispatch.

use super::*;

struct PreparedInherentMethod {
    method: InherentMethod,
    fn_ty: Ty,
    param_tys: Vec<Ty>,
    ret_ty: Ty,
    fn_ret: FuncReturn,
    initial_constraints: Vec<TraitConstraint>,
    has_receiver: bool,
}

struct CheckedInherentMethod {
    method: InherentMethod,
    fn_ty: Ty,
    constraints: Vec<TraitConstraint>,
    has_receiver: bool,
}

impl Infer {
    pub(super) fn export_inherent_method_schemes(
        &self,
    ) -> HashMap<String, HashMap<String, InherentMethodScheme>> {
        self.inherent
            .methods
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
            .traits
            .env
            .get(&id.trait_name)
            .ok_or_else(|| TypeError::UnknownTrait(id.trait_name.clone()))?
            .clone();

        if id.trait_args.len() != trait_def.params.len() {
            return Err(TypeError::TraitArityMismatch {
                trait_name: id.trait_name.clone(),
                expected: trait_def.params.len(),
                got: id.trait_args.len(),
            }
            .at(id.span));
        }
        if let Some(fundep) = trait_def.fundeps.first() {
            let expected_arrow_index = fundep.determinants.len();
            if id.fundep_arrow_index != Some(expected_arrow_index) {
                return Err(TypeError::InvalidTraitImplHead {
                    trait_name: id.trait_name.clone(),
                    message: format!(
                        "fundep trait impls must place `->` after {} determinant type argument{}",
                        expected_arrow_index,
                        if expected_arrow_index == 1 { "" } else { "s" }
                    ),
                }
                .at(id.span));
            }
        } else if id.used_fundep_arrow {
            return Err(TypeError::InvalidTraitImplHead {
                trait_name: id.trait_name.clone(),
                message: "`->` is only valid when the trait declares a functional dependency"
                    .to_string(),
            }
            .at(id.span));
        }

        let dict_indexes = trait_dict_indexes(&trait_def);
        id.dict_arg_indexes = dict_indexes.clone();
        validate_fundep_coverage(&trait_def, &id.trait_args, id.span)?;
        let impl_arg_keys = dict_indexes
            .iter()
            .map(|index| trait_impl_arg_keys_from_ast(&[id.trait_args[*index].clone()]))
            .collect::<Result<Vec<_>, _>>()
            .map(|keys| keys.into_iter().flatten().collect::<Vec<_>>())
            .map_err(|err| err.at(id.span))?;
        let impl_target = impl_arg_keys.join(", ");
        if trait_def.is_unary()
            && trait_uses_param_as_constructor(&trait_def)
            && matches!(id.trait_args.first(), Some(Type::App(_, _)))
            && !id.trait_args.first().is_some_and(type_has_hole)
        {
            let target = id
                .trait_args
                .first()
                .expect("unary trait impl has one checked trait argument");
            return Err(
                TypeError::InvalidTraitImplTarget(type_name_for_error_ast(target)).at(id.span),
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

        let dict_name =
            trait_impl_dict_name_for_indexes(&id.trait_name, &id.trait_args, &dict_indexes)
                .map_err(|err| err.at(id.span))?;
        let ambient = self.current_level;
        let (mut dict_fields, fn_constraints) = self.with_child_level(|this| {
            let mut impl_param_vars = HashMap::new();
            for arg in &id.trait_args {
                // Populate `impl_param_vars` with variables introduced by the impl head.
                let _ = this.ast_to_ty_with_vars(arg, &mut impl_param_vars)?;
            }
            let initial_constraints =
                this.collect_type_bound_constraints(&mut impl_param_vars, &id.type_bounds)?;
            let recursive_dict_ty = this.impl_trait_dict_ty(&trait_def, id, &impl_param_vars)?;
            let mut recursive_env = env.clone();
            recursive_env.insert(
                dict_name.clone(),
                EnvInfo::immutable(Scheme::mono(recursive_dict_ty)),
            );

            this.with_pending_constraints_scope(initial_constraints, |this| {
                let mut dict_fields: Vec<(String, Ty)> = Vec::new();
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
                        .map(|(_, t)| subst_trait_params(t, &trait_def, &id.trait_args))
                        .collect();
                    let derived_ret =
                        subst_trait_params(&trait_method.ret_type, &trait_def, &id.trait_args);

                    let mut param_vars: HashMap<String, TyVar> = impl_param_vars.clone();
                    let mut param_tys: Vec<Ty> = Vec::new();
                    let mut body_env = recursive_env.clone();

                    for (param, derived_ty) in impl_method.params.iter().zip(derived_params.iter())
                    {
                        if param.mut_place {
                            return Err(
                                TypeError::MutableFunctionCapabilityMismatch.at(impl_method.span)
                            );
                        }
                        if !is_irrefutable_param(&param.pat, &this.types.variant_env) {
                            return Err(TypeError::RefutableParamPattern.at(impl_method.body.span));
                        }
                        let p_ty = this.ast_to_ty_with_vars(derived_ty, &mut param_vars)?;
                        if let Some(p_type) = &param.ty {
                            let explicit_ty = this.ast_to_ty_with_vars(p_type, &mut param_vars)?;
                            unify(&mut this.subst, p_ty.clone(), explicit_ty)
                                .map_err(|err| err.at(impl_method.body.span))?;
                        }
                        param_tys.push(p_ty.clone());
                        this.check_pattern(&param.pat, p_ty, &mut body_env, false)?;
                    }
                    let ret_ty = this.ast_to_ty_with_vars(&derived_ret, &mut param_vars)?;

                    if let Some(ret_type_opt) = &impl_method.ret_type {
                        let explicit_ret =
                            this.ast_to_ty_with_vars(&ret_type_opt.ty, &mut param_vars)?;
                        unify(&mut this.subst, ret_ty.clone(), explicit_ret)
                            .map_err(|err| err.at(impl_method.body.span))?;
                    }

                    let fn_ret = value_func_return(ret_ty.clone());
                    let body_ty = this.with_fn_return_scope(fn_ret.clone(), |this| {
                        this.infer_expr(&body_env, &mut impl_method.body)
                    })?;
                    unify_expr_result(&mut this.subst, body_ty.clone(), ret_ty.clone())
                        .map_err(|err| err.at(impl_method.body.span))?;
                    if !matches!(this.subst.apply(&body_ty), Ty::Never) {
                        this.check_fresh_return_expr(&impl_method.body, &fn_ret)?;
                    }

                    let method_ty =
                        Ty::Func(value_func_params(param_tys), value_func_return(ret_ty));
                    this.metadata.record_definition_scheme(
                        impl_method.name_span,
                        Scheme::mono(method_ty.clone()),
                    );
                    dict_fields.push((impl_method.name.clone(), method_ty));
                }
                Ok(dict_fields)
            })
        })?;

        dict_fields.sort_by(|(a, _), (b, _)| a.cmp(b));
        let dict_ty = Ty::Record(Row {
            fields: dict_fields,
            tail: Box::new(Ty::Unit),
        });
        let finalized = self.finalize_constraints_at(env, dict_ty, fn_constraints, ambient);
        self.constraints.pending.extend(finalized.bubbled.clone());
        id.dict_params = finalized.owned.iter().map(dict_param_name).collect();
        let resolver = |p: &PendingDictArg| {
            resolve_local_or_concrete(
                p,
                &finalized.owned,
                env,
                &self.impls.known_dicts,
                &self.impls.known_schemes,
                &self.subst,
            )
        };
        for method in &mut id.methods {
            resolve_dict_uses_expr(&mut method.body, &resolver, false)?;
        }
        let dict_scheme = finalized.scheme;
        env.insert(dict_name, EnvInfo::immutable(dict_scheme));
        Ok(())
    }

    fn impl_trait_dict_ty(
        &mut self,
        trait_def: &TraitDef,
        id: &ImplDef,
        impl_param_vars: &HashMap<String, TyVar>,
    ) -> Result<Ty, SpannedTypeError> {
        let mut fields = Vec::new();
        for trait_method in &trait_def.methods {
            let derived_params = trait_method
                .params
                .iter()
                .map(|(_, ty)| subst_trait_params(ty, trait_def, &id.trait_args))
                .collect::<Vec<_>>();
            let derived_ret = subst_trait_params(&trait_method.ret_type, trait_def, &id.trait_args);
            let mut param_vars = impl_param_vars.clone();
            let param_tys = derived_params
                .iter()
                .map(|ty| self.ast_to_ty_with_vars(ty, &mut param_vars))
                .collect::<Result<Vec<_>, _>>()?;
            let ret_ty = self.ast_to_ty_with_vars(&derived_ret, &mut param_vars)?;
            fields.push((
                trait_method.name.clone(),
                Ty::Func(value_func_params(param_tys), value_func_return(ret_ty)),
            ));
        }
        fields.sort_by(|(a, _), (b, _)| a.cmp(b));
        Ok(Ty::Record(Row {
            fields,
            tail: Box::new(Ty::Unit),
        }))
    }

    pub(super) fn infer_inherent_impl(
        &mut self,
        env: &mut TypeEnv,
        id: &mut InherentImplDef,
    ) -> Result<(), SpannedTypeError> {
        let target_name = inherent_impl_target_key_from_ast(&id.target, &self.types.declared)
            .map_err(|err| err.at(id.span))?;
        let dict_name = inherent_impl_dict_name(&target_name);
        let mut seen_methods = HashSet::new();
        let mut dict_fields = Vec::new();
        for method in &id.methods {
            if !seen_methods.insert(method.name.clone())
                || self
                    .inherent
                    .methods
                    .get(&target_name)
                    .is_some_and(|methods| methods.contains_key(&method.name))
            {
                return Err(TypeError::DuplicateInherentMethod {
                    target: target_name.clone(),
                    method: method.name.clone(),
                }
                .at(method.name_span));
            }
        }

        let ambient = self.current_level;
        let checked_methods = self.with_child_level(|this| {
            let mut prepared_methods = Vec::with_capacity(id.methods.len());
            for method in &id.methods {
                prepared_methods.push(this.prepare_inherent_method(id, method)?);
            }

            let previous_methods = this.inherent.methods.get(&target_name).cloned();
            let mut provisional_methods = previous_methods.clone().unwrap_or_default();
            for prepared in &prepared_methods {
                provisional_methods.insert(
                    prepared.method.name.clone(),
                    InherentMethodInfo {
                        scheme: provisional_inherent_method_scheme(prepared),
                        resolved_callee: ResolvedCallee::InherentMethod {
                            dict: dict_name.clone(),
                            method: prepared.method.name.clone(),
                        },
                        has_receiver: prepared.has_receiver,
                    },
                );
            }
            this.inherent
                .methods
                .insert(target_name.clone(), provisional_methods);

            let result = (|| {
                let mut checked_methods = Vec::with_capacity(prepared_methods.len());
                for mut prepared in prepared_methods {
                    let mut body_env = env.clone();
                    for (param, p_ty) in
                        prepared.method.params.iter().zip(prepared.param_tys.iter())
                    {
                        this.check_param_pattern(
                            &param.pat,
                            p_ty.clone(),
                            &mut body_env,
                            param.mut_place,
                        )?;
                    }

                    let (_, constraints) = this.with_pending_constraints_scope(
                        prepared.initial_constraints.clone(),
                        |this| {
                            let body_ty = this
                                .with_fn_return_scope(prepared.fn_ret.clone(), |this| {
                                    this.infer_expr(&body_env, &mut prepared.method.body)
                                })?;
                            unify_expr_result(
                                &mut this.subst,
                                body_ty.clone(),
                                prepared.ret_ty.clone(),
                            )
                            .map_err(|err| err.at(prepared.method.body.span))?;
                            if !matches!(this.subst.apply(&body_ty), Ty::Never) {
                                this.check_fresh_return_expr(
                                    &prepared.method.body,
                                    &prepared.fn_ret,
                                )?;
                            }
                            Ok(())
                        },
                    )?;

                    checked_methods.push(CheckedInherentMethod {
                        method: prepared.method,
                        fn_ty: prepared.fn_ty,
                        constraints,
                        has_receiver: prepared.has_receiver,
                    });
                }
                Ok(checked_methods)
            })();

            match previous_methods {
                Some(methods) => {
                    this.inherent.methods.insert(target_name.clone(), methods);
                }
                None => {
                    this.inherent.methods.remove(&target_name);
                }
            }

            result
        })?;

        let mut inferred_methods = Vec::with_capacity(checked_methods.len());
        for checked in checked_methods {
            let mut inferred_method = checked.method;
            let fn_ty = checked.fn_ty;
            let finalized =
                self.finalize_constraints_at(env, fn_ty.clone(), checked.constraints, ambient);
            self.constraints.pending.extend(finalized.bubbled.clone());
            inferred_method.dict_params = finalized.owned.iter().map(dict_param_name).collect();

            let resolver = |p: &PendingDictArg| {
                resolve_local_or_concrete(
                    p,
                    &finalized.owned,
                    env,
                    &self.impls.known_dicts,
                    &self.impls.known_schemes,
                    &self.subst,
                )
            };
            resolve_dict_uses_expr(&mut inferred_method.body, &resolver, false)?;

            let scheme = finalized.scheme.clone();
            self.metadata
                .record_definition_scheme(inferred_method.name_span, scheme.clone());
            self.inherent
                .methods
                .entry(target_name.clone())
                .or_default()
                .insert(
                    inferred_method.name.clone(),
                    InherentMethodInfo {
                        scheme,
                        resolved_callee: ResolvedCallee::InherentMethod {
                            dict: dict_name.clone(),
                            method: inferred_method.name.clone(),
                        },
                        has_receiver: checked.has_receiver,
                    },
                );
            dict_fields.push((inferred_method.name.clone(), self.subst.apply(&fn_ty)));
            inferred_methods.push(inferred_method);
        }

        id.methods = inferred_methods;
        dict_fields.sort_by(|(a, _), (b, _)| a.cmp(b));
        env.insert(
            dict_name,
            EnvInfo::immutable(self.generalize_at(
                env,
                Ty::Record(Row {
                    fields: dict_fields,
                    tail: Box::new(Ty::Unit),
                }),
                ambient,
            )),
        );
        Ok(())
    }

    fn prepare_inherent_method(
        &mut self,
        id: &InherentImplDef,
        method: &InherentMethod,
    ) -> Result<PreparedInherentMethod, SpannedTypeError> {
        let has_receiver = method.params.first().is_some_and(is_self_param);
        let mut inferred_method = method.clone();
        substitute_self_in_inherent_method(&mut inferred_method, &id.target);

        let mut param_vars = HashMap::new();
        let target_ty = self.ast_to_ty_with_vars(&id.target, &mut param_vars)?;
        let mut initial_constraints =
            self.collect_type_bound_constraints(&mut param_vars, &id.type_bounds)?;
        initial_constraints.extend(
            self.collect_type_bound_constraints(&mut param_vars, &inferred_method.type_bounds)?,
        );
        let mut param_tys = Vec::new();

        for (idx, param) in inferred_method.params.iter().enumerate() {
            if !is_irrefutable_param(&param.pat, &self.types.variant_env) {
                return Err(TypeError::RefutableParamPattern.at(inferred_method.body.span));
            }
            let p_ty = if has_receiver && idx == 0 {
                let receiver_ty = target_ty.clone();
                if let Some(explicit) = &param.ty {
                    let explicit_ty = self.ast_to_ty_with_vars(explicit, &mut param_vars)?;
                    unify(&mut self.subst, receiver_ty.clone(), explicit_ty)
                        .map_err(|err| err.at(inferred_method.body.span))?;
                }
                receiver_ty
            } else {
                match &param.ty {
                    Some(t) => self.ast_to_ty_with_vars(t, &mut param_vars)?,
                    None => self.fresh_ty(),
                }
            };
            param_tys.push(p_ty);
        }

        let ret_ty = match &inferred_method.ret_type {
            Some(t) => self.ast_to_ty_with_vars(&t.ty, &mut param_vars)?,
            None => self.fresh_ty(),
        };
        let fn_ret = func_return_from_annotation(&inferred_method.ret_type, ret_ty.clone());
        let fn_ty = Ty::Func(
            func_params_from_params(&inferred_method.params, param_tys.clone()),
            fn_ret.clone(),
        );

        Ok(PreparedInherentMethod {
            method: inferred_method,
            fn_ty,
            param_tys,
            ret_ty,
            fn_ret,
            initial_constraints,
            has_receiver,
        })
    }
}

fn trait_uses_param_as_constructor(trait_def: &TraitDef) -> bool {
    let Some(param) = trait_def.primary_param() else {
        return false;
    };
    trait_def.methods.iter().any(|method| {
        method
            .params
            .iter()
            .any(|(_, ty)| type_uses_var_as_constructor(ty, param))
            || type_uses_var_as_constructor(&method.ret_type, param)
    })
}

fn subst_trait_params(ty: &Type, trait_def: &TraitDef, impl_args: &[Type]) -> Type {
    trait_def
        .params
        .iter()
        .zip(impl_args)
        .fold(ty.clone(), |acc, (param, arg)| {
            subst_hkt_param(&acc, param, arg)
        })
}

fn provisional_inherent_method_scheme(method: &PreparedInherentMethod) -> Scheme {
    let mut vars = free_type_vars(&method.fn_ty);
    for constraint in &method.initial_constraints {
        vars.insert(constraint.var);
        for arg in &constraint.args {
            free_type_vars_into(arg, &mut vars);
        }
    }
    let mut vars = vars.into_iter().collect::<Vec<_>>();
    vars.sort();
    Scheme {
        vars,
        constraints: method.initial_constraints.clone(),
        ty: method.fn_ty.clone(),
    }
}

fn validate_fundep_coverage(
    trait_def: &TraitDef,
    impl_args: &[Type],
    span: SourceSpan,
) -> Result<(), SpannedTypeError> {
    // Coverage is checked against the impl head because dictionary dispatch is
    // keyed by impl arguments. Method signatures are validated later by
    // `subst_trait_params` plus the per-method checks in `infer_impl`.
    for fundep in &trait_def.fundeps {
        let mut determinant_vars = HashSet::new();
        for index in &fundep.determinants {
            collect_type_vars(&impl_args[*index], &mut determinant_vars);
        }
        for index in &fundep.dependents {
            let mut dependent_vars = HashSet::new();
            collect_type_vars(&impl_args[*index], &mut dependent_vars);
            for var in dependent_vars {
                if !determinant_vars.contains(&var) {
                    return Err(TypeError::FunctionalDependencyViolation {
                        trait_name: trait_def.name.clone(),
                        message: format!(
                            "dependent type `{}` is not determined by determinant arguments",
                            var
                        ),
                    }
                    .at(span));
                }
            }
        }
    }
    Ok(())
}

fn collect_type_vars(ty: &Type, vars: &mut HashSet<String>) {
    walk_ast_type(ty, &mut |node| {
        if let Type::Var(var) = node {
            vars.insert(var.clone());
        }
    });
}

fn type_uses_var_as_constructor(ty: &Type, var_name: &str) -> bool {
    any_ast_type(
        ty,
        |node| matches!(node, Type::App(con, _) if matches!(con.as_ref(), Type::Var(name) if name == var_name)),
    )
}

fn type_has_hole(ty: &Type) -> bool {
    any_ast_type(ty, |node| matches!(node, Type::Hole))
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
