//! Scoped inference state and constraint finalization.
//!
//! Levels, pending trait constraints, and return stacks are temporary inference
//! state. This module provides restore-on-error helpers and decides which
//! constraints are owned, bubbled, or dropped at generalization boundaries.

use super::*;

#[derive(Debug, Clone)]
pub(super) struct FinalizedConstraints {
    pub(super) scheme: Scheme,
    pub(super) owned: Vec<TraitConstraint>,
    pub(super) bubbled: Vec<TraitConstraint>,
}

#[cfg(debug_assertions)]
fn levels_shadow_enabled() -> bool {
    static ENABLED: OnceLock<bool> = OnceLock::new();
    *ENABLED.get_or_init(|| {
        std::env::var("HERN_LEVELS_SHADOW")
            .map(|value| !value.is_empty() && value != "0")
            .unwrap_or(false)
    })
}

impl Infer {
    pub(super) fn with_child_level<T>(
        &mut self,
        f: impl FnOnce(&mut Self) -> Result<T, SpannedTypeError>,
    ) -> Result<T, SpannedTypeError> {
        let saved = self.current_level;
        self.current_level = self
            .current_level
            .checked_add(1)
            .expect("type inference level overflow");
        let result = f(self);
        self.current_level = saved;
        result
    }

    pub(super) fn generalize_at(&self, env: &TypeEnv, ty: Ty, ambient: TypeLevel) -> Scheme {
        let ty = self.subst.apply(&ty);
        let vars = self.level_generalizable_vars(&ty, ambient);
        #[cfg(debug_assertions)]
        self.report_level_generalization_shadow(env, &ty, ambient, &vars);
        #[cfg(not(debug_assertions))]
        let _ = env;
        // Constraints are set separately by finalize_constraints for Fn/Op.
        // For other uses (constructors, externs, let-values) there are no constraints.
        Scheme {
            vars,
            constraints: vec![],
            ty,
        }
    }

    pub(super) fn level_generalizable_vars(&self, ty: &Ty, ambient: TypeLevel) -> Vec<TyVar> {
        let mut vars: Vec<_> = free_type_vars(ty)
            .into_iter()
            .filter(|var| self.subst.level_of(*var) > ambient)
            .collect();
        vars.sort();
        vars
    }

    #[cfg(debug_assertions)]
    pub(super) fn report_level_generalization_shadow(
        &self,
        env: &TypeEnv,
        ty: &Ty,
        ambient: TypeLevel,
        level_vars: &[TyVar],
    ) {
        if !levels_shadow_enabled() {
            return;
        }
        let env_vars = self.generalizable_vars_by_env_scan(env, ty);
        if level_vars == env_vars {
            return;
        }
        eprintln!(
            "Hern levels shadow mismatch: ambient={}, env-scan={:?}, levels={:?}, ty={}",
            ambient, env_vars, level_vars, ty
        );
    }

    #[cfg(debug_assertions)]
    pub(super) fn generalizable_vars_by_env_scan(&self, env: &TypeEnv, ty: &Ty) -> Vec<TyVar> {
        let env_vars = env.free_vars(&self.subst);
        let ty_vars = free_type_vars(ty);
        let mut vars: Vec<TyVar> = ty_vars.difference(&env_vars).copied().collect();
        vars.sort();
        vars
    }

    #[cfg(test)]
    pub(super) fn normalized_free_vars_syntactic(&self, env: &TypeEnv) -> HashSet<TyVar> {
        env.free_vars_syntactic()
            .into_iter()
            .filter_map(|var| match self.subst.apply(&Ty::Var(var)) {
                Ty::Var(resolved) => Some(resolved),
                _ => None,
            })
            .collect()
    }

    pub(super) fn collect_type_bound_constraints(
        &mut self,
        param_vars: &mut HashMap<String, TyVar>,
        type_bounds: &[TypeBound],
    ) -> Result<Vec<TraitConstraint>, SpannedTypeError> {
        let mut constraints = Vec::new();
        for bound in type_bounds {
            let args = bound
                .args
                .iter()
                .map(|arg| self.ast_to_ty_with_vars(arg, param_vars))
                .collect::<Result<Vec<_>, _>>()?;
            for trait_name in &bound.traits {
                if let Some(trait_def) = self.traits.env.get(trait_name) {
                    let determinant_indexes = trait_dict_indexes(trait_def);
                    match (bound.fundep_arrow_index, trait_def.fundeps.is_empty()) {
                        (Some(_), true) => {
                            return Err(TypeError::InvalidTraitConstraint {
                                trait_name: trait_name.clone(),
                                message:
                                    "`->` is only valid when the trait declares a functional dependency"
                                        .to_string(),
                            }
                            .into());
                        }
                        (None, false) => {
                            return Err(TypeError::InvalidTraitConstraint {
                                trait_name: trait_name.clone(),
                                message: format!(
                                    "fundep trait constraints must include `->` between determinant and dependent type arguments; write `{}`",
                                    fundep_constraint_example(trait_def),
                                ),
                            }
                            .into());
                        }
                        _ => {}
                    }
                    if args.len() != trait_def.params.len() {
                        return Err(TypeError::TraitArityMismatch {
                            trait_name: trait_name.clone(),
                            expected: trait_def.params.len(),
                            got: args.len(),
                        }
                        .into());
                    }
                    if let Some(arrow_index) = bound.fundep_arrow_index
                        && arrow_index != determinant_indexes.len()
                    {
                        return Err(TypeError::InvalidTraitConstraint {
                            trait_name: trait_name.clone(),
                            message: format!(
                                "fundep constraints must place `->` after {} determinant type argument{}",
                                determinant_indexes.len(),
                                if determinant_indexes.len() == 1 { "" } else { "s" }
                            ),
                        }
                        .into());
                    }
                    let var = primary_trait_var(&args, &determinant_indexes)
                        .unwrap_or_else(|| self.fresh_var());
                    constraints.push(TraitConstraint::predicate(
                        trait_name.clone(),
                        args.clone(),
                        var,
                        determinant_indexes,
                    ));
                } else {
                    if bound.fundep_arrow_index.is_some() || args.len() != 1 {
                        return Err(TypeError::TraitArityMismatch {
                            trait_name: trait_name.clone(),
                            expected: 1,
                            got: args.len(),
                        }
                        .into());
                    }
                    let Ty::Var(var) = args[0].clone() else {
                        return Err(TypeError::InvalidTraitConstraint {
                            trait_name: trait_name.clone(),
                            message: "unary trait constraints must target a type variable"
                                .to_string(),
                        }
                        .into());
                    };
                    constraints.push(TraitConstraint::unary(var, trait_name.clone()));
                }
            }
        }
        Ok(constraints)
    }

    pub(super) fn with_pending_constraints_scope<T>(
        &mut self,
        initial_constraints: Vec<TraitConstraint>,
        f: impl FnOnce(&mut Self) -> Result<T, SpannedTypeError>,
    ) -> Result<(T, Vec<TraitConstraint>), SpannedTypeError> {
        let saved_pending = std::mem::take(&mut self.constraints.pending);
        self.constraints.pending.extend(initial_constraints);
        let result = f(self);
        let scoped_pending = std::mem::replace(&mut self.constraints.pending, saved_pending);
        // Failed scopes are discarded wholesale; constraints collected while
        // inferring an invalid body should not leak into the enclosing scope.
        result.map(|value| (value, scoped_pending))
    }

    pub(super) fn with_fn_return_scope<T>(
        &mut self,
        fn_ret: FuncReturn,
        f: impl FnOnce(&mut Self) -> Result<T, SpannedTypeError>,
    ) -> Result<T, SpannedTypeError> {
        self.flow.fn_return_tys.push(fn_ret);
        let result = f(self);
        self.flow.fn_return_tys.pop();
        result
    }

    /// Finalizes the constraints collected while inferring a function-like body.
    ///
    /// Constraints whose dispatch variable is generalized by this function become
    /// owned dictionary parameters. Constraints tied to an outer environment
    /// variable, or to a variable that was not generalized here, bubble back to
    /// the enclosing inference scope. Constraints already made concrete by
    /// substitution are intentionally dropped because they need no dictionary
    /// parameter.
    #[cfg(test)]
    pub(super) fn finalize_constraints(
        &self,
        env: &TypeEnv,
        fn_ty: Ty,
        fn_constraints: Vec<TraitConstraint>,
    ) -> FinalizedConstraints {
        self.finalize_constraints_at(env, fn_ty, fn_constraints, self.current_level)
    }

    pub(super) fn finalize_constraints_at(
        &self,
        env: &TypeEnv,
        fn_ty: Ty,
        fn_constraints: Vec<TraitConstraint>,
        ambient: TypeLevel,
    ) -> FinalizedConstraints {
        let mut scheme = self.generalize_at(env, fn_ty, ambient);
        let mut seen = HashSet::new();
        let mut seen_bubbled = HashSet::new();
        let mut owned = Vec::new();
        let mut bubbled = Vec::new();

        for constraint in fn_constraints {
            let normalized_var_ty = self.subst.apply(&Ty::Var(constraint.var));
            let normalized_args: Vec<Ty> = constraint
                .args
                .iter()
                .map(|arg| self.subst.apply(arg))
                .collect();
            let mut relevant_vars = HashSet::new();
            free_type_vars_into(&normalized_var_ty, &mut relevant_vars);
            for arg in &normalized_args {
                free_type_vars_into(arg, &mut relevant_vars);
            }

            if relevant_vars.is_empty() {
                // Fully concrete constraints do not become callable dictionary
                // parameters. Their pending dict uses are resolved by the
                // local/concrete resolver after inference has finished.
                continue;
            }

            let normalized_var = match normalized_var_ty {
                Ty::Var(var) => var,
                _ => constraint.var,
            };
            let normalized = TraitConstraint {
                var: normalized_var,
                trait_name: constraint.trait_name,
                args: normalized_args,
                determinant_indexes: constraint.determinant_indexes,
            };
            if relevant_vars.iter().all(|var| scheme.vars.contains(var)) {
                if seen.insert(normalized.clone()) {
                    owned.push(normalized);
                }
            } else if seen_bubbled.insert(normalized.clone()) {
                bubbled.push(normalized);
            }
        }

        scheme.constraints = owned.clone();
        FinalizedConstraints {
            scheme,
            owned,
            bubbled,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn syntactic_env_vars_are_normalized_before_constraint_partitioning() {
        let mut infer = Infer::new();
        let mut env = TypeEnv::new();
        env.insert(
            "outer".to_string(),
            EnvInfo::immutable(Scheme::mono(Ty::Var(0))),
        );

        infer.subst.bind_ty(0, Ty::Var(1)).expect("valid alias");

        assert_eq!(
            infer.normalized_free_vars_syntactic(&env),
            HashSet::from([1])
        );
    }

    #[test]
    fn level_generalization_quantifies_child_vars_only() {
        let mut infer = Infer::new();
        let outer = infer.subst.fresh_tyvar_at(ROOT_LEVEL);
        let local = infer.subst.fresh_tyvar_at(ROOT_LEVEL + 1);
        let mut env = TypeEnv::new();
        env.insert(
            "outer".to_string(),
            EnvInfo::immutable(Scheme::mono(Ty::Var(outer))),
        );

        let scheme = infer.generalize_at(
            &env,
            Ty::Tuple(vec![Ty::Var(outer), Ty::Var(local)]),
            ROOT_LEVEL,
        );

        assert_eq!(scheme.vars, vec![local]);
    }

    #[test]
    fn child_level_scope_restores_after_success_and_error() {
        let mut infer = Infer::new();
        assert_eq!(infer.current_level, ROOT_LEVEL);

        let var = infer
            .with_child_level(|infer| {
                assert_eq!(infer.current_level, ROOT_LEVEL + 1);
                Ok(infer.fresh_var())
            })
            .expect("scope should succeed");

        assert_eq!(infer.current_level, ROOT_LEVEL);
        assert_eq!(infer.subst.level_of(var), ROOT_LEVEL + 1);

        let result: Result<(), SpannedTypeError> = infer.with_child_level(|infer| {
            assert_eq!(infer.current_level, ROOT_LEVEL + 1);
            Err(TypeError::UnboundVariable("boom".to_string()).at(SourceSpan::synthetic()))
        });

        assert!(result.is_err());
        assert_eq!(infer.current_level, ROOT_LEVEL);
    }

    #[test]
    fn level_generalizable_vars_use_ambient_level() {
        let mut infer = Infer::new();
        let outer = infer.subst.fresh_tyvar_at(ROOT_LEVEL);
        let inner = infer.subst.fresh_tyvar_at(ROOT_LEVEL + 1);
        let ty = Ty::Tuple(vec![Ty::Var(outer), Ty::Var(inner)]);

        assert_eq!(infer.level_generalizable_vars(&ty, ROOT_LEVEL), vec![inner]);
    }

    #[test]
    fn concrete_constraints_are_resolved_without_callable_dict_params() {
        let mut infer = Infer::new();
        let var = infer.subst.fresh_tyvar_at(ROOT_LEVEL + 1);
        infer
            .subst
            .bind_ty(var, Ty::Float)
            .expect("valid concrete type");

        let finalized = infer.finalize_constraints(
            &TypeEnv::new(),
            Ty::Func(
                value_func_params(vec![Ty::Float]),
                value_func_return(Ty::Float),
            ),
            vec![TraitConstraint {
                var,
                trait_name: "Add".to_string(),
                args: vec![Ty::Var(var)],
                determinant_indexes: vec![0],
            }],
        );

        assert!(finalized.owned.is_empty());
        assert!(finalized.bubbled.is_empty());
        assert!(finalized.scheme.constraints.is_empty());
    }

    #[test]
    fn constraint_on_outer_env_var_bubbles_from_function_scope() {
        let infer = Infer::new();
        let mut env = TypeEnv::new();
        env.insert(
            "outer".to_string(),
            EnvInfo::immutable(Scheme::mono(Ty::Var(0))),
        );

        let finalized = infer.finalize_constraints(
            &env,
            Ty::Func(
                value_func_params(vec![Ty::Var(0)]),
                value_func_return(Ty::Int),
            ),
            vec![TraitConstraint::unary(0, "Show".to_string())],
        );

        assert!(finalized.owned.is_empty());
        assert_eq!(
            finalized.bubbled,
            vec![TraitConstraint::unary(0, "Show".to_string())]
        );
        assert!(finalized.scheme.constraints.is_empty());
    }

    #[test]
    fn constraint_on_non_generalized_var_bubbles_from_function_scope() {
        let mut infer = Infer::new();
        let receiver = infer.subst.fresh_tyvar_at(ROOT_LEVEL + 1);
        let key = infer.subst.fresh_tyvar_at(ROOT_LEVEL + 1);
        let output = infer.subst.fresh_tyvar_at(ROOT_LEVEL + 1);
        let constraint = TraitConstraint::predicate(
            "Index",
            vec![Ty::Var(receiver), Ty::Var(key), Ty::Var(output)],
            output,
            vec![0, 1],
        );

        let finalized = infer.finalize_constraints(
            &TypeEnv::new(),
            Ty::Func(
                value_func_params(vec![Ty::Var(receiver), Ty::Var(key)]),
                value_func_return(Ty::Int),
            ),
            vec![constraint.clone()],
        );

        assert!(finalized.owned.is_empty());
        assert_eq!(finalized.bubbled, vec![constraint]);
        assert!(finalized.scheme.constraints.is_empty());
    }

    #[test]
    fn constraint_with_concrete_primary_and_local_args_is_owned() {
        let mut infer = Infer::new();
        let receiver = infer.subst.fresh_tyvar_at(ROOT_LEVEL + 1);
        let key = infer.subst.fresh_tyvar_at(ROOT_LEVEL + 1);
        let output = infer.subst.fresh_tyvar_at(ROOT_LEVEL + 1);
        infer
            .subst
            .bind_ty(output, Ty::Con("string".to_string()))
            .expect("valid concrete output");

        let constraint = TraitConstraint::predicate(
            "Index",
            vec![Ty::Var(receiver), Ty::Var(key), Ty::Var(output)],
            output,
            vec![0, 1],
        );
        let finalized = infer.finalize_constraints(
            &TypeEnv::new(),
            Ty::Func(
                value_func_params(vec![Ty::Var(receiver), Ty::Var(key)]),
                value_func_return(Ty::Con("string".to_string())),
            ),
            vec![constraint],
        );

        assert_eq!(
            finalized.owned,
            vec![TraitConstraint::predicate(
                "Index",
                vec![
                    Ty::Var(receiver),
                    Ty::Var(key),
                    Ty::Con("string".to_string())
                ],
                output,
                vec![0, 1],
            )]
        );
        assert!(finalized.bubbled.is_empty());
        assert_eq!(finalized.scheme.constraints, finalized.owned);
    }

    #[test]
    fn scoped_inference_state_restores_after_error() {
        let mut infer = Infer::new();
        infer
            .constraints
            .pending
            .push(TraitConstraint::unary(0, "Outer".to_string()));

        let err = infer
            .with_pending_constraints_scope(
                vec![TraitConstraint::unary(1, "Inner".to_string())],
                |this| {
                    this.constraints
                        .pending
                        .push(TraitConstraint::unary(2, "Body".to_string()));
                    Err::<(), SpannedTypeError>(TypeError::UnknownType("boom".to_string()).into())
                },
            )
            .expect_err("scope body should fail");

        assert!(matches!(err.error.as_ref(), TypeError::UnknownType(_)));
        assert_eq!(
            infer.constraints.pending,
            vec![TraitConstraint::unary(0, "Outer".to_string())]
        );

        let err = infer
            .with_fn_return_scope(value_func_return(Ty::Int), |_this| {
                Err::<(), SpannedTypeError>(TypeError::UnknownType("return".to_string()).into())
            })
            .expect_err("return scope body should fail");
        assert!(matches!(err.error.as_ref(), TypeError::UnknownType(_)));
        assert!(infer.flow.fn_return_tys.is_empty());
    }
}
