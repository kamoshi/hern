//! Expression inference dispatch.
//!
//! This module routes expression forms to the narrower rule modules, records
//! expression metadata, and keeps expected-type inference close to the normal
//! expression path.

use super::*;

impl Infer {
    pub(super) fn infer_expr_expected(
        &mut self,
        env: &TypeEnv,
        expr: &mut Expr,
        expected: Ty,
    ) -> Result<Ty, SpannedTypeError> {
        let expected = self.subst.apply(&expected);
        let expr_span = expr.span;
        let expr_id = expr.id;
        match &mut expr.kind {
            ExprKind::Grouped(inner) => {
                let ty = self.infer_expr_expected(env, inner, expected)?;
                return Ok(self.record_expr_type_for_node(expr_id, ty));
            }
            ExprKind::Array(entries) => {
                let ty = self.infer_array_entries(env, entries, Some(expected), expr_span)?;
                return Ok(self.record_expr_type_for_node(expr_id, ty));
            }
            ExprKind::If {
                cond,
                then_branch,
                else_branch,
            } => {
                let cond_ty = self.infer_expr(env, cond)?;
                unify(&mut self.subst, cond_ty, Ty::Con("bool".to_string()))?;
                let then_ty = self.infer_expr_expected(env, then_branch, expected.clone())?;
                let else_ty = self.infer_expr_expected(env, else_branch, expected.clone())?;
                let combined = combine_branch_types(&mut self.subst, then_ty, else_ty)?;
                unify(&mut self.subst, combined, expected.clone())
                    .map_err(|err| err.at(expr_span))?;
                let ty = self.subst.apply(&expected);
                return Ok(self.record_expr_type_for_node(expr_id, ty));
            }
            ExprKind::Match { scrutinee, arms } => {
                let scrutinee_ty = self.infer_expr(env, scrutinee)?;
                let mut result_ty = None;
                let match_scrutinee_ty = self.subst.apply(&scrutinee_ty);
                for (pattern, arm_expr) in &mut *arms {
                    let mut arm_env = env.clone();
                    let scrutinee_before_pattern = self.subst.apply(&scrutinee_ty);
                    self.check_pattern(
                        pattern,
                        scrutinee_before_pattern.clone(),
                        &mut arm_env,
                        false,
                    )?;
                    let scrutinee_after_pattern = self.subst.apply(&scrutinee_ty);
                    let arm_ty = self
                        .infer_expr_expected(&arm_env, arm_expr, expected.clone())
                        .map_err(|err| {
                            constructor_pattern_refinement_mismatch(
                                pattern,
                                match_scrutinee_ty.clone(),
                                scrutinee_after_pattern.clone(),
                                err,
                                arm_expr.span,
                            )
                        })?;
                    result_ty = Some(match result_ty {
                        Some(existing) => combine_branch_types(&mut self.subst, existing, arm_ty)?,
                        None => arm_ty,
                    });
                }
                let s_ty = self.subst.apply(&scrutinee_ty);
                self.check_exhaustive(arms, &s_ty)?;
                if let Some(result_ty) = result_ty {
                    unify(&mut self.subst, result_ty, expected.clone())
                        .map_err(|err| err.at(expr_span))?;
                }
                let ty = self.subst.apply(&expected);
                return Ok(self.record_expr_type_for_node(expr_id, ty));
            }
            ExprKind::Lambda {
                params,
                return_type,
                body,
                dict_params,
            } => {
                if let Ty::Func(expected_params, expected_ret) = expected.clone() {
                    let ty = self.infer_lambda_expr(
                        env,
                        expr_id,
                        params,
                        return_type.as_ref(),
                        body,
                        dict_params,
                        Some((expected_params, expected_ret)),
                    )?;
                    return Ok(self.record_expr_type_for_node(expr_id, ty));
                }
            }
            ExprKind::Call {
                callee,
                args,
                is_method_call,
                arg_wrappers,
                resolved_callee,
                pending_trait_method,
                dict_args,
                pending_dict_args,
            } => {
                if let ExprKind::FieldAccess { expr, field, .. } = &mut callee.kind {
                    let ty = self.resolve_receiver_call(
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
                        Some(expected),
                    )?;
                    return Ok(self.record_expr_type_for_node(expr_id, ty));
                }
                let _ = pending_trait_method;
            }
            _ => {}
        }

        let actual = self.infer_expr(env, expr)?;
        unify_expr_result(&mut self.subst, actual, expected.clone())
            .map_err(|err| err.at(expr_span))?;
        let ty = self.subst.apply(&expected);
        Ok(self.record_expr_type_for_node(expr_id, ty))
    }

    pub(super) fn infer_expr(
        &mut self,
        env: &TypeEnv,
        expr: &mut Expr,
    ) -> Result<Ty, SpannedTypeError> {
        let expr_id = expr.id;
        let result: Result<Ty, SpannedTypeError> = match &mut expr.kind {
            ExprKind::Grouped(inner) => self.infer_expr(env, inner),
            ExprKind::Number(n) => match n {
                crate::lex::NumberLiteral::Int(_) => Ok(Ty::Int),
                crate::lex::NumberLiteral::Float(_) => Ok(Ty::Float),
            },
            ExprKind::StringLit(_) => Ok(Ty::Con("string".to_string())),
            ExprKind::Bool(_) => Ok(Ty::Con("bool".to_string())),
            ExprKind::Not(operand) => {
                let op_ty = self.infer_expr(env, operand)?;
                unify(&mut self.subst, op_ty, Ty::Con("bool".to_string()))?;
                Ok(Ty::Con("bool".to_string()))
            }
            ExprKind::Neg {
                operand,
                resolved_op,
                pending_op,
                ..
            } => self.infer_neg_expr(env, operand, resolved_op, pending_op),
            ExprKind::Unit => Ok(Ty::Unit),
            ExprKind::Import(path) => self
                .imports
                .types
                .get(path)
                .cloned()
                .ok_or_else(|| TypeError::UnknownImport(path.clone()).into()),
            ExprKind::Ident(name) => env
                .get(name)
                .map(|info| {
                    let instantiated = self.instantiate_scheme(&info.scheme);
                    let ty = if instantiated.constraints.is_empty() {
                        instantiated.ty
                    } else {
                        Ty::Qualified(instantiated.constraints, Box::new(instantiated.ty))
                    };
                    if expr.id != NO_NODE_ID {
                        self.metadata.record_symbol_type(expr.id, ty.clone());
                        self.metadata.record_binding_capability(
                            expr.span,
                            BindingCapabilities {
                                place_mutable: info.is_place_mutable(),
                            },
                        );
                        if matches!(self.subst.apply(&info.scheme.ty), Ty::Func(_, _)) {
                            self.metadata.record_callable_capabilities(
                                expr.id,
                                scheme_param_capabilities(&info.scheme),
                            );
                        }
                    }
                    ty
                })
                .ok_or_else(|| TypeError::UnboundVariable(name.clone()).into()),
            ExprKind::Assign { target, value } => {
                let target_ty = match &mut target.kind {
                    ExprKind::Ident(name) => {
                        let info = env
                            .get(name)
                            .ok_or_else(|| TypeError::UnboundVariable(name.clone()))?;
                        if !info.is_binding_mutable() {
                            return Err(TypeError::ImmutableAssignment(name.clone()).into());
                        }
                        let ty = self.instantiate(&info.scheme);
                        if target.id != NO_NODE_ID {
                            self.metadata.record_symbol_type(target.id, ty.clone());
                        }
                        ty
                    }
                    ExprKind::FieldAccess { .. } => {
                        let Some(name) = find_assignment_base_name(target) else {
                            return Err(TypeError::InvalidAssignmentTarget.into());
                        };
                        let info = env
                            .get(&name)
                            .ok_or_else(|| TypeError::UnboundVariable(name.clone()))?;
                        if !info.is_place_mutable() {
                            return Err(TypeError::ImmutablePlace(name).into());
                        }
                        self.infer_expr(env, target)?
                    }
                    _ => unreachable!("Parser validates assignment targets"),
                };
                let value_ty = self.infer_expr(env, value)?;
                unify(&mut self.subst, target_ty, value_ty)?;
                Ok(Ty::Unit)
            }
            ExprKind::Binary {
                lhs,
                op,
                rhs,
                resolved_op,
                pending_op,
                dict_args,
                pending_dict_args,
                ..
            } => self.infer_binary_expr(
                env,
                lhs,
                op,
                rhs,
                resolved_op,
                pending_op,
                dict_args,
                pending_dict_args,
            ),
            ExprKind::Range {
                start,
                end,
                inclusive,
            } => self.infer_range_expr(env, start.as_deref_mut(), end.as_deref_mut(), *inclusive),
            ExprKind::Call {
                callee,
                args,
                is_method_call,
                arg_wrappers,
                resolved_callee,
                pending_trait_method,
                dict_args,
                pending_dict_args,
            } => self.infer_call_expr(
                env,
                expr_id,
                expr.span,
                callee,
                args,
                is_method_call,
                arg_wrappers,
                resolved_callee,
                pending_trait_method,
                dict_args,
                pending_dict_args,
            ),
            ExprKind::AssociatedAccess {
                target,
                target_span,
                member,
                member_span,
                resolution,
            } => {
                match self.associated_trait_method(target, member, *member_span) {
                    Ok(Some(lookup)) => {
                        let instance = self.instantiate_associated_trait_method(
                            env,
                            &lookup.trait_def,
                            &lookup.method,
                            lookup.explicit_args.as_deref(),
                            *target_span,
                        )?;
                        *resolution = Some(AssociatedAccessResolution::TraitMethod {
                            method: instance.method,
                            dict: instance.dict,
                        });
                        let ty = instance.value_ty;
                        self.record_symbol_type(expr.id, ty.clone());
                        return Ok(ty);
                    }
                    Ok(None) => {}
                    Err(trait_err) if is_unknown_trait_method_error(&trait_err) => {
                        if let Ok((_, method_info)) = self.associated_inherent_method(
                            target,
                            *target_span,
                            member,
                            *member_span,
                        ) {
                            let instance = self.instantiate_associated_inherent_method(
                                target,
                                *target_span,
                                &method_info,
                            )?;
                            *resolution = Some(AssociatedAccessResolution::Inherent(
                                instance.resolved_callee,
                            ));
                            let ty = instance.value_ty;
                            self.record_symbol_type(expr.id, ty.clone());
                            return Ok(ty);
                        }
                        return Err(trait_err);
                    }
                    Err(err) => return Err(err),
                }
                let (_, method_info) =
                    self.associated_inherent_method(target, *target_span, member, *member_span)?;
                let instance = self.instantiate_associated_inherent_method(
                    target,
                    *target_span,
                    &method_info,
                )?;
                *resolution = Some(AssociatedAccessResolution::Inherent(
                    instance.resolved_callee,
                ));
                let ty = instance.value_ty;
                self.record_symbol_type(expr.id, ty.clone());
                Ok(ty)
            }
            ExprKind::If {
                cond,
                then_branch,
                else_branch,
            } => {
                let cond_ty = self.infer_expr(env, cond)?;
                unify(&mut self.subst, cond_ty, Ty::Con("bool".to_string()))?;
                let then_ty = self.infer_expr(env, then_branch)?;
                let else_ty = self.infer_expr(env, else_branch)?;
                combine_branch_types(&mut self.subst, then_ty, else_ty).map_err(|err| err.into())
            }
            ExprKind::Match { scrutinee, arms } => {
                let scrutinee_ty = self.infer_expr(env, scrutinee)?;
                let mut result_ty = None;
                let match_scrutinee_ty = self.subst.apply(&scrutinee_ty);
                for (pattern, arm_expr) in &mut *arms {
                    let mut arm_env = env.clone();
                    let scrutinee_before_pattern = self.subst.apply(&scrutinee_ty);
                    self.check_pattern(
                        pattern,
                        scrutinee_before_pattern.clone(),
                        &mut arm_env,
                        false,
                    )?;
                    let scrutinee_after_pattern = self.subst.apply(&scrutinee_ty);
                    let arm_ty = self.infer_expr(&arm_env, arm_expr).map_err(|err| {
                        constructor_pattern_refinement_mismatch(
                            pattern,
                            match_scrutinee_ty.clone(),
                            scrutinee_after_pattern.clone(),
                            err,
                            arm_expr.span,
                        )
                    })?;
                    result_ty = Some(match result_ty {
                        Some(existing) => combine_branch_types(&mut self.subst, existing, arm_ty)?,
                        None => arm_ty,
                    });
                }
                let s_ty = self.subst.apply(&scrutinee_ty);
                self.check_exhaustive(arms, &s_ty)?;
                Ok(result_ty.unwrap_or(Ty::Never))
            }
            ExprKind::Loop(body) => {
                let break_ty = self.fresh_ty();
                self.with_loop_break_scope(break_ty.clone(), |this| {
                    let _body_ty = this.infer_expr(env, body)?;
                    Ok(())
                })?;
                Ok(break_ty)
            }
            ExprKind::Break(val) => {
                let break_ty = self
                    .flow
                    .loop_break_tys
                    .last()
                    .cloned()
                    .ok_or(TypeError::BreakOutsideLoop)?;
                if let Some(val_expr) = val {
                    let val_ty = self.infer_expr(env, val_expr)?;
                    unify_expr_result(&mut self.subst, val_ty, break_ty)?;
                } else {
                    unify(&mut self.subst, break_ty, Ty::Unit)?;
                }
                Ok(Ty::Never)
            }
            ExprKind::Continue => {
                if self.flow.loop_break_tys.is_empty() {
                    Err(TypeError::ContinueOutsideLoop.into())
                } else {
                    Ok(Ty::Never)
                }
            }
            ExprKind::Return(val) => {
                let ret = self
                    .flow
                    .fn_return_tys
                    .last()
                    .cloned()
                    .ok_or(TypeError::ReturnOutsideFunction)?;
                if let Some(val_expr) = val {
                    let val_ty = self.infer_expr(env, val_expr)?;
                    unify_expr_result(&mut self.subst, val_ty, (*ret.ty).clone())?;
                    self.check_fresh_return_expr(val_expr, &ret)?;
                } else {
                    unify(&mut self.subst, (*ret.ty).clone(), Ty::Unit)?;
                }
                Ok(Ty::Never)
            }
            ExprKind::Block { stmts, final_expr } => {
                let mut block_env = env.clone();
                for stmt in stmts.iter_mut() {
                    self.infer_stmt(&mut block_env, stmt)?;
                    if stmt_always_exits(stmt, true) {
                        return Ok(self.fresh_ty());
                    }
                }
                match final_expr {
                    Some(expr) => self.infer_expr(&block_env, expr),
                    None => Ok(Ty::Unit),
                }
            }
            ExprKind::Tuple(exprs) => {
                let tys: Vec<Ty> = exprs
                    .iter_mut()
                    .map(|e| self.infer_expr(env, e))
                    .collect::<Result<_, _>>()?;
                Ok(Ty::Tuple(tys))
            }
            ExprKind::Array(entries) => self.infer_array_entries(env, entries, None, expr.span),
            ExprKind::Record(entries) => self.infer_record_expr(env, entries, expr.span),
            ExprKind::FieldAccess {
                expr: base, field, ..
            } => {
                let field_access_id = expr_id;
                let imported_member_scheme = self.imported_member_scheme(base, field);
                let imported_callable_capabilities = imported_member_scheme
                    .as_ref()
                    .filter(|scheme| matches!(scheme.ty, Ty::Func(_, _)))
                    .map(scheme_param_capabilities);
                let local_field_callable_capabilities =
                    if let ExprKind::Ident(base_name) = &base.kind {
                        self.inherent
                            .record_field_callables
                            .get(base_name)
                            .and_then(|fields| fields.get(field))
                            .cloned()
                    } else {
                        None
                    };
                // Keep base inference before the imported-member fast path so
                // hover/signature metadata for the module binding is still
                // recorded and an invalid receiver is rejected normally.
                let expr_ty = self.infer_expr(env, base)?;
                if let Some(scheme) = imported_member_scheme {
                    let instantiated = self.instantiate_scheme(&scheme);
                    let ty = if instantiated.constraints.is_empty() {
                        instantiated.ty
                    } else {
                        Ty::Qualified(instantiated.constraints, Box::new(instantiated.ty))
                    };
                    if let Some(param_capabilities) = imported_callable_capabilities {
                        self.record_callable_capabilities(field_access_id, param_capabilities);
                    }
                    return Ok(ty);
                }
                let field_ty = self.fresh_ty();
                let tail = self.fresh_ty();
                let expected = Ty::Record(Row {
                    fields: vec![(field.clone(), field_ty.clone())],
                    tail: Box::new(tail),
                });
                unify(&mut self.subst, expr_ty, expected)?;
                if let Some(param_capabilities) =
                    imported_callable_capabilities.or(local_field_callable_capabilities)
                {
                    self.record_callable_capabilities(field_access_id, param_capabilities);
                }
                Ok(field_ty)
            }
            ExprKind::Index {
                receiver,
                key,
                resolved_callee,
                pending_trait_method,
                dict_args,
                pending_dict_args,
            } => self.infer_index_expr(
                env,
                receiver,
                key,
                resolved_callee,
                pending_trait_method,
                dict_args,
                pending_dict_args,
            ),
            ExprKind::Lambda {
                params,
                return_type,
                body,
                dict_params,
            } => self.infer_lambda_expr(
                env,
                expr_id,
                params,
                return_type.as_ref(),
                body,
                dict_params,
                None,
            ),
            ExprKind::For {
                pat,
                iterable,
                body,
                resolved_iter,
                pending_iter,
            } => self.infer_for_expr(env, pat, iterable, body, resolved_iter, pending_iter),
        };
        if let Ok(ty) = &result
            && expr.id != NO_NODE_ID
        {
            self.metadata.record_expr_type(expr.id, ty.clone());
        }
        result.map_err(|err: SpannedTypeError| err.with_span_if_absent(expr.span))
    }
}

pub(super) fn constructor_pattern_refinement_mismatch(
    pattern: &Pattern,
    scrutinee_before_pattern: Ty,
    scrutinee_after_pattern: Ty,
    err: SpannedTypeError,
    span: SourceSpan,
) -> SpannedTypeError {
    if !matches!(pattern, Pattern::Constructor { .. })
        || !matches!(err.error.as_ref(), TypeError::OccursCheck(_))
        || scrutinee_before_pattern == scrutinee_after_pattern
    {
        return err;
    }

    TypeError::Mismatch {
        expected: scrutinee_after_pattern,
        got: scrutinee_before_pattern,
    }
    .at(span)
}
