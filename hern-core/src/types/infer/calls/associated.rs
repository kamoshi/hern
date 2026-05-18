//! Associated function and method lookup for call inference.
//!
//! This module resolves `Type::member` and trait-associated calls into callable
//! types plus the dictionary metadata needed by later application.

use super::*;

impl Infer {
    pub(in crate::types::infer) fn associated_inherent_method(
        &self,
        target: &Type,
        target_span: SourceSpan,
        member: &str,
        member_span: SourceSpan,
    ) -> Result<(String, InherentMethodInfo), SpannedTypeError> {
        let target_names = inherent_impl_target_keys_from_ast(target, &self.types.declared)
            .map_err(|err| err.at(target_span))?;
        for target_name in &target_names {
            let method_info = self
                .inherent
                .methods
                .get(target_name)
                .and_then(|methods| methods.get(member))
                .or_else(|| {
                    self.inherent
                        .scoped_methods
                        .get(target_name)
                        .and_then(|methods| methods.get(member))
                })
                .cloned();
            if let Some(method_info) = method_info {
                return Ok((target_name.clone(), method_info));
            }
        }
        Err(TypeError::UnknownAssociatedFunction {
            target: target_names[0].clone(),
            function: member.to_string(),
        }
        .at(member_span))
    }

    pub(in crate::types::infer) fn instantiate_associated_inherent_method(
        &mut self,
        target: &Type,
        target_span: SourceSpan,
        method_info: &InherentMethodInfo,
    ) -> Result<AssociatedInherentMethodInstance, SpannedTypeError> {
        let instantiated = self.instantiate_scheme(&method_info.scheme);
        let mut callable_ty = instantiated.ty;
        let mut constraints = instantiated.constraints;
        if let Ty::Qualified(existing, inner) = callable_ty {
            constraints.extend(existing);
            callable_ty = *inner;
        }
        if method_info.has_receiver && matches!(target, Type::App(..)) {
            // Bare `Type::method` stays generic; its receiver is pinned when the
            // function value is called. Explicit `Type(Args)::method` should
            // specialize the receiver immediately.
            let receiver_ty = self
                .ast_to_ty_with_vars(target, &mut HashMap::new())
                .map_err(|err| err.at(target_span))?;
            let Some(receiver_param) = func_receiver_param(&callable_ty) else {
                return Err(TypeError::NotAFunction(callable_ty).at(target_span));
            };
            unify(&mut self.subst, receiver_param, receiver_ty)
                .map_err(|err| err.at(target_span))?;
            callable_ty = self.subst.apply(&callable_ty);
        }
        let value_ty = if constraints.is_empty() {
            callable_ty.clone()
        } else {
            Ty::Qualified(constraints.clone(), Box::new(callable_ty.clone()))
        };
        Ok(AssociatedInherentMethodInstance {
            callable_ty,
            constraints,
            value_ty,
            resolved_callee: method_info.resolved_callee.clone(),
        })
    }

    pub(in crate::types::infer) fn associated_trait_method(
        &self,
        target: &Type,
        member: &str,
        member_span: SourceSpan,
    ) -> Result<Option<AssociatedTraitMethodLookup>, SpannedTypeError> {
        let Type::Ident(trait_name) = target else {
            if let Type::App(con, args) = target
                && let Type::Ident(trait_name) = con.as_ref()
                && let Some(trait_def) = self.traits.env.get(trait_name).cloned()
            {
                let method = trait_def
                    .methods
                    .iter()
                    .find(|method| method.name == member)
                    .ok_or_else(|| {
                        TypeError::UnknownTraitMethod {
                            trait_name: trait_name.clone(),
                            method: member.to_string(),
                        }
                        .at(member_span)
                    })?
                    .clone();
                return Ok(Some(AssociatedTraitMethodLookup {
                    trait_def,
                    method,
                    explicit_args: Some(args.clone()),
                }));
            }
            return Ok(None);
        };
        let Some(trait_def) = self.traits.env.get(trait_name).cloned() else {
            return Ok(None);
        };
        let method = trait_def
            .methods
            .iter()
            .find(|method| method.name == member)
            .ok_or_else(|| {
                TypeError::UnknownTraitMethod {
                    trait_name: trait_name.clone(),
                    method: member.to_string(),
                }
                .at(member_span)
            })?
            .clone();
        Ok(Some(AssociatedTraitMethodLookup {
            trait_def,
            method,
            explicit_args: None,
        }))
    }

    pub(in crate::types::infer) fn instantiate_associated_trait_method(
        &mut self,
        env: &TypeEnv,
        trait_def: &TraitDef,
        method: &TraitMethod,
        explicit_args: Option<&[Type]>,
        target_span: SourceSpan,
    ) -> Result<AssociatedTraitMethodInstance, SpannedTypeError> {
        let mut param_vars = HashMap::new();
        let trait_arg_tys = if let Some(args) = explicit_args {
            if args.len() != trait_def.params.len() {
                return Err(TypeError::TraitArityMismatch {
                    trait_name: trait_def.name.clone(),
                    expected: trait_def.params.len(),
                    got: args.len(),
                }
                .at(target_span));
            }
            trait_def
                .params
                .iter()
                .zip(args)
                .map(|(param, arg)| {
                    let ty = self.ast_to_ty_with_vars(arg, &mut param_vars)?;
                    if let Ty::Var(var) = ty {
                        param_vars.insert(param.clone(), var);
                    }
                    Ok(ty)
                })
                .collect::<Result<Vec<_>, TypeError>>()
                .map_err(|err| err.at(target_span))?
        } else {
            trait_def
                .params
                .iter()
                .map(|param| {
                    let var = self.fresh_var();
                    param_vars.insert(param.clone(), var);
                    Ty::Var(var)
                })
                .collect()
        };

        let method_param_types = if let Some(args) = explicit_args {
            method
                .params
                .iter()
                .map(|(_, ty)| {
                    trait_def
                        .params
                        .iter()
                        .zip(args)
                        .fold(ty.clone(), |acc, (param, arg)| {
                            subst_hkt_param(&acc, param, arg)
                        })
                })
                .collect::<Vec<_>>()
        } else {
            method
                .params
                .iter()
                .map(|(_, ty)| ty.clone())
                .collect::<Vec<_>>()
        };
        let method_ret_type = if let Some(args) = explicit_args {
            trait_def
                .params
                .iter()
                .zip(args)
                .fold(method.ret_type.clone(), |acc, (param, arg)| {
                    subst_hkt_param(&acc, param, arg)
                })
        } else {
            method.ret_type.clone()
        };

        let method_param_tys = method_param_types
            .iter()
            .map(|ty| self.ast_to_ty_with_vars(ty, &mut param_vars))
            .collect::<Result<Vec<_>, _>>()
            .map_err(|err| err.at(target_span))?;
        let ret_ty = self
            .ast_to_ty_with_vars(&method_ret_type, &mut param_vars)
            .map_err(|err| err.at(target_span))?;
        let callable_ty = Ty::Func(
            value_func_params(method_param_tys),
            value_func_return(ret_ty),
        );
        let determinant_indexes = trait_dict_indexes(trait_def);
        let dict = if explicit_args.is_some() {
            Some(
                resolve_concrete_from_args_unifying(
                    &trait_def.name,
                    &trait_arg_tys,
                    &determinant_indexes,
                    env,
                    &self.impls.known_dicts,
                    &self.impls.known_schemes,
                    &mut self.subst,
                )
                .ok_or_else(|| {
                    TypeError::MissingTraitImpl {
                        trait_name: trait_def.name.clone(),
                        impl_target: trait_arg_tys
                            .iter()
                            .map(|ty| ty.to_string())
                            .collect::<Vec<_>>()
                            .join(", "),
                    }
                    .at(target_span)
                })?,
            )
        } else {
            None
        };
        let constraints = if dict.is_none() {
            let var = primary_trait_var(&trait_arg_tys, &determinant_indexes)
                .or_else(|| trait_arg_tys.iter().find_map(first_ty_var))
                .ok_or_else(|| {
                    TypeError::UnresolvedTrait {
                        context: "trait method value".to_string(),
                        trait_name: trait_def.name.clone(),
                    }
                    .at(target_span)
                })?;
            vec![TraitConstraint::predicate(
                &trait_def.name,
                trait_arg_tys,
                var,
                determinant_indexes,
            )]
        } else {
            Vec::new()
        };
        let value_ty = if constraints.is_empty() {
            callable_ty.clone()
        } else {
            Ty::Qualified(constraints.clone(), Box::new(callable_ty.clone()))
        };
        Ok(AssociatedTraitMethodInstance {
            callable_ty,
            constraints,
            value_ty,
            dict,
            method: method.name.clone(),
        })
    }

    #[allow(clippy::too_many_arguments)]
    pub(in crate::types::infer) fn resolve_associated_call(
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
        let (_target_name, method_info) =
            self.associated_inherent_method(target, target_span, member, member_span)?;
        let instance =
            self.instantiate_associated_inherent_method(target, target_span, &method_info)?;
        self.record_symbol_type(callee_id, instance.value_ty.clone());

        let param_capabilities = match &instance.callable_ty {
            Ty::Func(params, _) => func_param_capabilities(params),
            _ => Vec::new(),
        };
        let applied = self.apply_callable_type(
            env,
            args,
            arg_wrappers,
            instance.callable_ty.clone(),
            instance.constraints,
            Vec::new(),
            param_capabilities,
            0,
            member_span,
            dict_args,
            pending_dict_args,
        )?;
        self.record_symbol_type(callee_id, applied.call_ty);
        *resolved_callee = Some(instance.resolved_callee);
        if applied.fresh_return && call_expr_id != NO_NODE_ID {
            self.metadata.mark_fresh_place(call_expr_id);
        }
        Ok(applied.ret_ty)
    }
}

fn func_receiver_param(ty: &Ty) -> Option<Ty> {
    match ty {
        Ty::Func(params, _) => params.first().map(|param| param.ty.clone()),
        Ty::Qualified(_, inner) => func_receiver_param(inner),
        _ => None,
    }
}
