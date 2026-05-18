//! Inference for `for` loops and `Iterable` dispatch.
//!
//! A `for` loop type-checks by resolving the iterable expression against the
//! `Iterable` trait, deriving the yielded element type from `iter`, binding the
//! loop pattern against that element type, and checking the body for effects
//! while the loop expression itself has unit type.

use super::*;

impl Infer {
    pub(super) fn infer_for_expr(
        &mut self,
        env: &TypeEnv,
        pat: &mut Pattern,
        iterable: &mut Expr,
        body: &mut Expr,
        resolved_iter: &mut Option<ResolvedCallee>,
        pending_iter: &mut Option<PendingDictArg>,
    ) -> Result<Ty, SpannedTypeError> {
        let iter_ty = self.infer_expr(env, iterable)?;

        let iterable_trait = self
            .traits
            .env
            .get("Iterable")
            .ok_or_else(|| TypeError::UnknownTrait("Iterable".to_string()))?
            .clone();
        let iter_method = iterable_trait
            .methods
            .iter()
            .find(|m| m.name == "iter")
            .ok_or_else(|| TypeError::UnknownTraitMethod {
                trait_name: "Iterable".to_string(),
                method: "iter".to_string(),
            })?
            .clone();

        let mut param_vars: HashMap<String, TyVar> = HashMap::new();
        let target_var = self.fresh_var();
        let iterable_param = primary_param_or_panic(&iterable_trait);
        param_vars.insert(iterable_param.to_string(), target_var);

        let self_ty = self.ast_to_ty_with_vars(&iter_method.params[0].1, &mut param_vars)?;
        let ret_ty = self.ast_to_ty_with_vars(&iter_method.ret_type, &mut param_vars)?;

        unify(&mut self.subst, iter_ty, self_ty)?;

        let resolved_target = self.subst.apply(&Ty::Var(target_var));
        self.resolve_iterable_dict(env, resolved_iter, pending_iter, resolved_target)
            .map_err(|err| err.with_span_if_absent(iterable.span))?;

        let elem_ty = match self.subst.apply(&ret_ty) {
            Ty::App(_, args) if args.len() == 1 => args.into_iter().next().unwrap(),
            other => other,
        };

        let mut body_env = env.clone();
        let elem_ty_applied = self.subst.apply(&elem_ty);
        self.check_pattern(pat, elem_ty_applied, &mut body_env, false)?;

        self.flow.loop_break_tys.push(Ty::Unit);
        self.infer_expr(&body_env, body)?;
        self.flow.loop_break_tys.pop();

        Ok(Ty::Unit)
    }

    pub(super) fn resolve_iterable_dict(
        &mut self,
        env: &TypeEnv,
        resolved_iter: &mut Option<ResolvedCallee>,
        pending_iter: &mut Option<PendingDictArg>,
        resolved_target: Ty,
    ) -> Result<(), SpannedTypeError> {
        let target_keys = trait_impl_target_keys_from_ty(&resolved_target);
        if target_keys.is_empty() {
            return match resolved_target {
                Ty::Var(v) => {
                    self.constraints
                        .pending
                        .push(TraitConstraint::unary(v, "Iterable".to_string()));
                    *pending_iter = Some(PendingDictArg {
                        var: v,
                        trait_name: "Iterable".to_string(),
                        args: vec![Ty::Var(v)],
                        determinant_indexes: vec![0],
                    });
                    Ok(())
                }
                _ => Err(TypeError::UnresolvedTrait {
                    context: "for loop".to_string(),
                    trait_name: "Iterable".to_string(),
                }
                .into()),
            };
        }

        let dict_name = target_keys
            .into_iter()
            .map(|key| trait_impl_dict_name("Iterable", &key))
            .find(|dict_name| {
                env.get(dict_name).is_some() || self.impls.known_dicts.contains(dict_name)
            });
        match dict_name {
            Some(dict_name) => {
                *resolved_iter = Some(ResolvedCallee::DictMethod {
                    dict: DictRef::Concrete(dict_name),
                    method: "iter".to_string(),
                });
                Ok(())
            }
            None => Err(TypeError::MissingTraitImpl {
                trait_name: "Iterable".to_string(),
                impl_target: format!("{}", resolved_target),
            }
            .into()),
        }
    }
}
