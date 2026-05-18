//! Inference for unary and binary operators.
//!
//! Operators are lowered through well-known traits and methods, then checked like
//! trait-dispatched calls. This module owns operator-specific arity and operand
//! rules; indexing lives separately because its receiver/key/output relation is
//! a distinct multi-parameter trait rule.

use super::*;

pub(super) struct OperatorTraitMethodTypes {
    trait_args: Vec<Ty>,
    lhs_param_ty: Ty,
    rhs_param_ty: Ty,
    ret_ty: Ty,
}

pub(super) struct UnaryOperatorTraitMethodTypes {
    trait_args: Vec<Ty>,
    operand_param_ty: Ty,
    ret_ty: Ty,
}

impl Infer {
    #[allow(clippy::too_many_arguments)]
    pub(super) fn infer_binary_expr(
        &mut self,
        env: &TypeEnv,
        lhs: &mut Expr,
        op: &BinOp,
        rhs: &mut Expr,
        resolved_op: &mut Option<ResolvedCallee>,
        pending_op: &mut Option<PendingDictArg>,
        dict_args: &mut Vec<DictRef>,
        pending_dict_args: &mut Vec<PendingDictArg>,
    ) -> Result<Ty, SpannedTypeError> {
        let l_ty = self.infer_expr(env, lhs)?;
        match op {
            BinOp::Pipe => self.infer_pipe_expr(env, lhs, rhs, l_ty, dict_args, pending_dict_args),
            BinOp::Custom(op) => self.infer_custom_binary_expr(
                env,
                op,
                rhs,
                l_ty,
                resolved_op,
                pending_op,
                dict_args,
                pending_dict_args,
            ),
        }
    }

    pub(super) fn infer_pipe_expr(
        &mut self,
        env: &TypeEnv,
        lhs: &mut Expr,
        rhs: &mut Expr,
        l_ty: Ty,
        dict_args: &mut Vec<DictRef>,
        pending_dict_args: &mut Vec<PendingDictArg>,
    ) -> Result<Ty, SpannedTypeError> {
        let r_ty = self.infer_expr(env, rhs)?;
        if let ExprKind::Ident(callee_name) = &rhs.kind
            && let Some(info) = env.get(callee_name.as_str())
        {
            let scheme = info.scheme.clone();
            if scheme_param_capability(&scheme, 0).is_mut_place() {
                self.check_mutable_place_arg(env, lhs, 0)?;
            }
            if !scheme.constraints.is_empty() {
                return self.infer_constrained_apply(
                    env,
                    &scheme,
                    vec![l_ty],
                    dict_args,
                    pending_dict_args,
                );
            }
        }
        let ret_var = self.fresh_var();
        let expected_r_ty = Ty::Func(
            value_func_params(vec![l_ty]),
            value_func_return(Ty::Var(ret_var)),
        );
        unify(&mut self.subst, r_ty, expected_r_ty)?;
        Ok(self.subst.apply(&Ty::Var(ret_var)))
    }

    pub(super) fn infer_neg_expr(
        &mut self,
        env: &TypeEnv,
        operand: &mut Expr,
        resolved_op: &mut Option<ResolvedCallee>,
        pending_op: &mut Option<PendingDictArg>,
    ) -> Result<Ty, SpannedTypeError> {
        const TRAIT_NAME: &str = "Neg";
        const METHOD_NAME: &str = "-";

        let trait_def = self
            .traits
            .env
            .get(TRAIT_NAME)
            .ok_or_else(|| TypeError::UnknownTrait(TRAIT_NAME.to_string()))?
            .clone();
        let method = trait_def
            .methods
            .iter()
            .find(|method| method.name == METHOD_NAME)
            .ok_or_else(|| TypeError::UnknownTraitMethod {
                trait_name: TRAIT_NAME.to_string(),
                method: METHOD_NAME.to_string(),
            })?
            .clone();
        if method.params.len() != 1 {
            return Err(TypeError::TraitMethodArityMismatch {
                trait_name: TRAIT_NAME.to_string(),
                method: METHOD_NAME.to_string(),
                expected: 1,
                got: method.params.len(),
            }
            .into());
        }

        let UnaryOperatorTraitMethodTypes {
            trait_args,
            operand_param_ty,
            ret_ty,
        } = self.instantiate_unary_operator_trait_method(&trait_def, &method)?;
        if !trait_def.is_unary() {
            return Err(TypeError::TraitArityMismatch {
                trait_name: TRAIT_NAME.to_string(),
                expected: 1,
                got: trait_def.params.len(),
            }
            .into());
        }
        let target_var = operator_trait_target_var(&trait_def, &trait_args)?;

        let operand_ty = self.infer_expr_expected(env, operand, operand_param_ty.clone())?;
        unify(&mut self.subst, operand_ty, operand_param_ty)?;
        let resolved_target = self.subst.apply(&Ty::Var(target_var));
        self.resolve_operator_dispatch(
            env,
            TRAIT_NAME,
            METHOD_NAME,
            &resolved_target,
            resolved_op,
            pending_op,
            &mut Vec::new(),
            &mut Vec::new(),
        )?;
        Ok(self.subst.apply(&ret_ty))
    }

    #[allow(clippy::too_many_arguments)]
    pub(super) fn infer_custom_binary_expr(
        &mut self,
        env: &TypeEnv,
        op: &str,
        rhs: &mut Expr,
        l_ty: Ty,
        resolved_op: &mut Option<ResolvedCallee>,
        pending_op: &mut Option<PendingDictArg>,
        dict_args: &mut Vec<DictRef>,
        pending_dict_args: &mut Vec<PendingDictArg>,
    ) -> Result<Ty, SpannedTypeError> {
        if let Some(trait_name) = self.traits.op_trait_map.get(op).cloned() {
            self.infer_trait_operator_expr(
                env,
                op,
                rhs,
                l_ty,
                &trait_name,
                resolved_op,
                pending_op,
                dict_args,
                pending_dict_args,
            )
        } else {
            self.infer_function_operator_expr(
                env,
                op,
                rhs,
                l_ty,
                resolved_op,
                dict_args,
                pending_dict_args,
            )
        }
    }

    #[allow(clippy::too_many_arguments)]
    pub(super) fn infer_trait_operator_expr(
        &mut self,
        env: &TypeEnv,
        op: &str,
        rhs: &mut Expr,
        l_ty: Ty,
        trait_name: &str,
        resolved_op: &mut Option<ResolvedCallee>,
        pending_op: &mut Option<PendingDictArg>,
        dict_args: &mut Vec<DictRef>,
        pending_dict_args: &mut Vec<PendingDictArg>,
    ) -> Result<Ty, SpannedTypeError> {
        let trait_def = self
            .traits
            .env
            .get(trait_name)
            .ok_or_else(|| TypeError::UnknownTrait(trait_name.to_string()))?
            .clone();
        let method = trait_def
            .methods
            .iter()
            .find(|m| m.name == op)
            .ok_or_else(|| TypeError::UnknownTraitMethod {
                trait_name: trait_name.to_string(),
                method: op.to_string(),
            })?
            .clone();
        if method.params.len() != 2 {
            return Err(TypeError::TraitMethodArityMismatch {
                trait_name: trait_name.to_string(),
                method: op.to_string(),
                expected: 2,
                got: method.params.len(),
            }
            .into());
        }

        let OperatorTraitMethodTypes {
            trait_args,
            lhs_param_ty,
            rhs_param_ty,
            ret_ty,
        } = self.instantiate_operator_trait_method(&trait_def, &method)?;

        if trait_def.is_unary() {
            let target_var = operator_trait_target_var(&trait_def, &trait_args)?;
            unify(&mut self.subst, l_ty, lhs_param_ty)?;
            let rhs_param_ty = self.subst.apply(&rhs_param_ty);
            let r_ty = self.infer_expr_expected(env, rhs, rhs_param_ty.clone())?;
            unify(&mut self.subst, r_ty, rhs_param_ty)?;

            let resolved_target = self.subst.apply(&Ty::Var(target_var));
            self.resolve_operator_dispatch(
                env,
                trait_name,
                op,
                &resolved_target,
                resolved_op,
                pending_op,
                dict_args,
                pending_dict_args,
            )?;
            return Ok(self.subst.apply(&ret_ty));
        }

        unify(&mut self.subst, l_ty.clone(), lhs_param_ty)?;
        let rhs_param_ty = self.subst.apply(&rhs_param_ty);
        let r_ty = self.infer_expr_expected(env, rhs, rhs_param_ty.clone())?;
        unify(&mut self.subst, r_ty.clone(), rhs_param_ty.clone())?;

        let trait_args = trait_args
            .iter()
            .map(|arg| self.subst.apply(arg))
            .collect::<Vec<_>>();
        let determinant_indexes = trait_dict_indexes(&trait_def);
        self.apply_matching_pending_trait_constraint(trait_name, &trait_args, &determinant_indexes);
        let trait_args_post = trait_args
            .iter()
            .map(|arg| self.subst.apply(arg))
            .collect::<Vec<_>>();
        let mut pending_trait_method = None;
        if let Some(ret_ty) = self.resolve_multi_param_trait_dispatch(
            env,
            trait_name,
            op,
            trait_args_post.clone(),
            determinant_indexes.clone(),
            vec![self.subst.apply(&l_ty), self.subst.apply(&rhs_param_ty)],
            ret_ty,
            resolved_op,
            &mut pending_trait_method,
            "operator trait dictionaries should be concrete",
        )? {
            if let Some((pending, _)) = pending_trait_method {
                *pending_op = Some(pending);
            }
            return Ok(ret_ty);
        }

        let determinant_args = determinant_indexes
            .iter()
            .filter_map(|index| trait_args_post.get(*index))
            .collect::<Vec<_>>();
        if determinant_args
            .iter()
            .all(|arg| free_type_vars(arg).is_empty())
        {
            return Err(TypeError::MissingTraitImpl {
                trait_name: trait_name.to_string(),
                impl_target: determinant_args
                    .iter()
                    .map(|arg| arg.to_string())
                    .collect::<Vec<_>>()
                    .join(", "),
            }
            .into());
        }

        Err(TypeError::UnresolvedTrait {
            context: "operator".to_string(),
            trait_name: trait_name.to_string(),
        }
        .into())
    }

    pub(super) fn apply_matching_pending_trait_constraint(
        &mut self,
        trait_name: &str,
        trait_args: &[Ty],
        determinant_indexes: &[usize],
    ) {
        for index in 0..self.constraints.pending.len() {
            let constraint = &self.constraints.pending[index];
            if constraint.trait_name != trait_name
                || constraint.args.len() != trait_args.len()
                || constraint.determinant_indexes != determinant_indexes
                || !determinants_share_var(
                    &constraint.args,
                    trait_args,
                    determinant_indexes,
                    &self.subst,
                )
            {
                continue;
            }

            let mut trial = self.subst.clone();
            if constraint
                .args
                .iter()
                .cloned()
                .zip(trait_args.iter().cloned())
                .all(|(constraint_arg, trait_arg)| {
                    unify(&mut trial, constraint_arg, trait_arg).is_ok()
                })
            {
                self.subst = trial;
                debug_assert!(
                    self.remaining_pending_trait_matches_are_compatible(
                        index + 1,
                        trait_name,
                        trait_args,
                        determinant_indexes,
                    ),
                    "multiple pending fundep predicates matched but were not equivalent"
                );
                return;
            }
        }
    }

    pub(super) fn remaining_pending_trait_matches_are_compatible(
        &self,
        start_index: usize,
        trait_name: &str,
        trait_args: &[Ty],
        determinant_indexes: &[usize],
    ) -> bool {
        for constraint in self.constraints.pending.iter().skip(start_index) {
            if constraint.trait_name != trait_name
                || constraint.args.len() != trait_args.len()
                || constraint.determinant_indexes != determinant_indexes
                || !determinants_share_var(
                    &constraint.args,
                    trait_args,
                    determinant_indexes,
                    &self.subst,
                )
            {
                continue;
            }

            let mut trial = self.subst.clone();
            if !constraint
                .args
                .iter()
                .cloned()
                .zip(trait_args.iter().cloned())
                .all(|(constraint_arg, trait_arg)| {
                    unify(&mut trial, constraint_arg, trait_arg).is_ok()
                })
            {
                return false;
            }
        }
        true
    }

    pub(super) fn instantiate_operator_trait_method(
        &mut self,
        trait_def: &TraitDef,
        method: &TraitMethod,
    ) -> Result<OperatorTraitMethodTypes, SpannedTypeError> {
        ensure_operator_trait_has_params(trait_def)?;
        let mut param_vars: HashMap<String, TyVar> = HashMap::new();
        let trait_args = trait_def
            .params
            .iter()
            .map(|param| {
                let var = self.fresh_var();
                param_vars.insert(param.clone(), var);
                Ty::Var(var)
            })
            .collect::<Vec<_>>();

        Ok(OperatorTraitMethodTypes {
            trait_args,
            lhs_param_ty: self.ast_to_ty_with_vars(&method.params[0].1, &mut param_vars)?,
            rhs_param_ty: self.ast_to_ty_with_vars(&method.params[1].1, &mut param_vars)?,
            ret_ty: self.ast_to_ty_with_vars(&method.ret_type, &mut param_vars)?,
        })
    }

    pub(super) fn instantiate_unary_operator_trait_method(
        &mut self,
        trait_def: &TraitDef,
        method: &TraitMethod,
    ) -> Result<UnaryOperatorTraitMethodTypes, SpannedTypeError> {
        ensure_operator_trait_has_params(trait_def)?;
        let mut param_vars: HashMap<String, TyVar> = HashMap::new();
        let trait_args = trait_def
            .params
            .iter()
            .map(|param| {
                let var = self.fresh_var();
                param_vars.insert(param.clone(), var);
                Ty::Var(var)
            })
            .collect::<Vec<_>>();

        Ok(UnaryOperatorTraitMethodTypes {
            trait_args,
            operand_param_ty: self.ast_to_ty_with_vars(&method.params[0].1, &mut param_vars)?,
            ret_ty: self.ast_to_ty_with_vars(&method.ret_type, &mut param_vars)?,
        })
    }

    #[allow(clippy::too_many_arguments)]
    pub(super) fn infer_function_operator_expr(
        &mut self,
        env: &TypeEnv,
        op: &str,
        rhs: &mut Expr,
        l_ty: Ty,
        resolved_op: &mut Option<ResolvedCallee>,
        dict_args: &mut Vec<DictRef>,
        pending_dict_args: &mut Vec<PendingDictArg>,
    ) -> Result<Ty, SpannedTypeError> {
        let r_ty = self.infer_expr(env, rhs)?;
        if let Some(info) = env.get(op) {
            let scheme = info.scheme.clone();
            if !scheme.constraints.is_empty() {
                let ret_ty = self.infer_constrained_apply(
                    env,
                    &scheme,
                    vec![l_ty, r_ty],
                    dict_args,
                    pending_dict_args,
                )?;
                *resolved_op = Some(ResolvedCallee::Function(op.to_string()));
                return Ok(ret_ty);
            }
        }
        let fn_ty = env
            .get(op)
            .map(|info| self.instantiate(&info.scheme))
            .ok_or_else(|| TypeError::UnboundVariable(op.to_string()))?;
        let ret_var = self.fresh_var();
        let expected = Ty::Func(
            value_func_params(vec![l_ty, r_ty]),
            value_func_return(Ty::Var(ret_var)),
        );
        unify(&mut self.subst, fn_ty, expected)?;
        Ok(self.subst.apply(&Ty::Var(ret_var)))
    }
}
