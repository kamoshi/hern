//! Function, method, and trait-call inference.
//!
//! Calls are where plain function application, receiver methods, associated
//! methods, mutable-place requirements, and dictionary arguments meet. This
//! module preserves the call-shaped flow so overload and trait dispatch decisions
//! remain visible in one place.

use super::*;

mod apply;
mod associated;
mod dispatch;
mod receiver;

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

pub(super) struct AssociatedInherentMethodInstance {
    pub(super) callable_ty: Ty,
    pub(super) constraints: Vec<TraitConstraint>,
    pub(super) value_ty: Ty,
    pub(super) resolved_callee: ResolvedCallee,
}

pub(super) struct AssociatedTraitMethodInstance {
    pub(super) callable_ty: Ty,
    pub(super) constraints: Vec<TraitConstraint>,
    pub(super) value_ty: Ty,
    pub(super) dict: Option<DictRef>,
    pub(super) method: String,
}

pub(super) struct AssociatedTraitMethodLookup {
    pub(super) trait_def: TraitDef,
    pub(super) method: TraitMethod,
    pub(super) explicit_args: Option<Vec<Type>>,
}

#[derive(Clone)]
struct ReceiverTraitMethodMatch {
    trait_def: TraitDef,
    method: TraitMethod,
}

struct ReceiverTraitMethodResolution {
    ret_ty: Ty,
    resolved_callee: ResolvedCallee,
}

impl Infer {
    #[allow(clippy::too_many_arguments)]
    pub(super) fn infer_call_expr(
        &mut self,
        env: &TypeEnv,
        expr_id: NodeId,
        expr_span: SourceSpan,
        callee: &mut Box<Expr>,
        args: &mut [Expr],
        is_method_call: &mut bool,
        arg_wrappers: &mut Vec<Option<ArgWrapper>>,
        resolved_callee: &mut Option<ResolvedCallee>,
        pending_trait_method: &mut Option<(PendingDictArg, String)>,
        dict_args: &mut Vec<DictRef>,
        pending_dict_args: &mut Vec<PendingDictArg>,
    ) -> Result<Ty, SpannedTypeError> {
        if let ExprKind::AssociatedAccess {
            target,
            target_span,
            member,
            member_span,
            ..
        } = &callee.kind
        {
            match self.associated_trait_method(target, member, *member_span) {
                Ok(Some(lookup)) => {
                    if lookup.explicit_args.is_none() {
                        return self.resolve_trait_method_call(
                            env,
                            callee.id,
                            args,
                            arg_wrappers,
                            resolved_callee,
                            pending_trait_method,
                            lookup.trait_def,
                            lookup.method,
                            "trait method call",
                        );
                    }
                    let instance = self.instantiate_associated_trait_method(
                        env,
                        &lookup.trait_def,
                        &lookup.method,
                        lookup.explicit_args.as_deref(),
                        *target_span,
                    )?;
                    let param_capabilities = match &instance.callable_ty {
                        Ty::Func(params, _) => func_param_capabilities(params),
                        _ => Vec::new(),
                    };
                    let applied = self.apply_callable_type(
                        env,
                        args,
                        arg_wrappers,
                        instance.callable_ty,
                        instance.constraints,
                        Vec::new(),
                        None,
                        param_capabilities,
                        0,
                        *member_span,
                        dict_args,
                        pending_dict_args,
                    )?;
                    self.record_symbol_type(callee.id, applied.call_ty);
                    if let Some(dict) = instance.dict {
                        *resolved_callee = Some(ResolvedCallee::DictMethod {
                            dict,
                            method: instance.method,
                        });
                    }
                    if applied.fresh_return && expr_id != NO_NODE_ID {
                        self.metadata.mark_fresh_place(expr_id);
                    }
                    return Ok(applied.ret_ty);
                }
                Ok(None) => {}
                Err(trait_err) if is_unknown_trait_method_error(&trait_err) => {
                    match self.resolve_associated_call(
                        env,
                        expr_id,
                        callee.id,
                        target,
                        *target_span,
                        member,
                        *member_span,
                        args,
                        arg_wrappers,
                        resolved_callee,
                        dict_args,
                        pending_dict_args,
                    ) {
                        Ok(ty) => return Ok(ty),
                        Err(inherent_err)
                            if matches!(
                                inherent_err.error.as_ref(),
                                TypeError::UnknownAssociatedFunction { .. }
                                    | TypeError::InvalidInherentImplTarget(_)
                            ) =>
                        {
                            return Err(trait_err);
                        }
                        Err(inherent_err) => return Err(inherent_err),
                    }
                }
                Err(err) => return Err(err),
            }

            return self.resolve_associated_call(
                env,
                expr_id,
                callee.id,
                target,
                *target_span,
                member,
                *member_span,
                args,
                arg_wrappers,
                resolved_callee,
                dict_args,
                pending_dict_args,
            );
        }

        if let ExprKind::FieldAccess { expr, field, .. } = &mut callee.kind {
            return self.resolve_receiver_call(
                env,
                expr_id,
                callee.id,
                expr,
                field,
                args,
                is_method_call,
                arg_wrappers,
                resolved_callee,
                dict_args,
                pending_dict_args,
                None,
            );
        }

        if let ExprKind::Ident(callee_name) = &callee.kind
            && let Some(info) = env.get(callee_name.as_str())
        {
            let scheme = info.scheme.clone();
            if !scheme.constraints.is_empty() {
                // Qualified values need dictionary arguments attached during
                // application. Inferring the callee expression first would strip
                // the `Ty::Qualified` wrapper and lose the constraints before
                // `apply_scheme_callable` can turn them into dict args.
                if callee.id != NO_NODE_ID {
                    let instantiated = self.instantiate_value(&scheme);
                    self.metadata.record_symbol_type(callee.id, instantiated);
                }
                let applied = self.apply_scheme_callable(
                    env,
                    args,
                    arg_wrappers,
                    &scheme,
                    Vec::new(),
                    None,
                    0,
                    dict_args,
                    pending_dict_args,
                )?;
                if applied.fresh_return && expr_id != NO_NODE_ID {
                    self.metadata.mark_fresh_place(expr_id);
                }
                return Ok(applied.ret_ty);
            }
        }

        let mut callee_ty = self.infer_expr(env, callee)?;
        callee_ty = self.subst.apply(&callee_ty);
        let callee_constraints = if let Ty::Qualified(constraints, inner) = callee_ty {
            callee_ty = *inner;
            constraints
        } else {
            Vec::new()
        };
        let param_capabilities = match &callee_ty {
            Ty::Func(params, _) => func_param_capabilities(params),
            _ => self.callable_capabilities_for(callee.id),
        };
        let applied = self.apply_callable_type(
            env,
            args,
            arg_wrappers,
            callee_ty,
            callee_constraints,
            Vec::new(),
            None,
            param_capabilities,
            0,
            expr_span,
            dict_args,
            pending_dict_args,
        )?;
        if applied.fresh_return && expr_id != NO_NODE_ID {
            self.metadata.mark_fresh_place(expr_id);
        }
        Ok(applied.ret_ty)
    }
}
