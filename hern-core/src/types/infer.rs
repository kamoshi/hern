mod calls;
mod decls;
mod dicts;
mod impls;
mod metadata;
mod recovery;
mod snapshot;

use self::dicts::{
    attach_dict_args, dict_param_name, dict_ref_concrete_name, final_pass_stmt, resolve_concrete,
    resolve_concrete_dict_ref, resolve_concrete_from_args_unifying,
    resolve_concrete_multi_dict_ref, resolve_dict_uses_expr, resolve_dict_uses_expr_lenient,
    resolve_local_or_concrete,
};
use super::{
    patterns::{
        check_exhaustive_match, insert_pattern_bindings, is_irrefutable_let, is_irrefutable_param,
    },
    type_syntax::{
        inherent_impl_dict_name, inherent_impl_target_key_from_ast,
        inherent_impl_target_keys_from_ast, inherent_impl_target_keys_from_ty, is_self_param,
        record_field_ty, subst_hkt_param, substitute_self_in_inherent_method, trait_dict_indexes,
        trait_impl_arg_keys_from_ast, trait_impl_dict_name, trait_impl_dict_name_for_indexes,
        trait_impl_dict_name_from_keys, trait_impl_target_keys_from_ty,
    },
};
use crate::ast::*;
use crate::types::{
    BindingCapabilities, CallableCapabilities, EnvInfo, FuncParam, FuncReturn,
    InherentMethodScheme, ParamCapability, ROOT_LEVEL, ReturnCapability, Row, Scheme, Subst,
    TraitConstraint, Ty, TyVar, TypeLevel, display_ty_with_var_names,
    env::build_variant_env_from_stmts,
    error::{SpannedTypeError, TypeError, TypeMismatchContext},
    free_type_vars, free_type_vars_in_display_order, free_type_vars_into, perf, type_var_name,
    unify, value_func_params, value_func_return,
};
pub use crate::types::{TypeEnv, VariantEnv, VariantInfo, is_fresh_mutable_place, is_value};
#[cfg(debug_assertions)]
use std::sync::OnceLock;

const INDEX_TRAIT_ARITY: usize = 3;
use metadata::{FinalizedTypeMaps, TypeMetadata};
use recovery::{CollectedNames, stmt_bound_names, stmt_referenced_names};
use snapshot::InferSnapshot;
use std::collections::{HashMap, HashSet};

const NO_NODE_ID: NodeId = 0;

struct ResolvedTraitMethod {
    trait_def: TraitDef,
    method: TraitMethod,
}

#[derive(Debug, Clone)]
struct InherentMethodInfo {
    scheme: Scheme,
    resolved_callee: ResolvedCallee,
    has_receiver: bool,
}

// ── Infer ─────────────────────────────────────────────────────────────────────

pub struct Infer {
    subst: Subst,
    trait_env: HashMap<String, TraitDef>,
    variant_env: VariantEnv,
    type_aliases: HashMap<String, (Vec<String>, Type)>,
    declared_types: HashSet<String>,
    scoped_declared_types: HashSet<String>,
    op_trait_map: HashMap<String, String>,
    inherent_methods: HashMap<String, HashMap<String, InherentMethodInfo>>,
    scoped_inherent_methods: HashMap<String, HashMap<String, InherentMethodInfo>>,
    import_types: HashMap<String, Ty>,
    import_schemes: HashMap<String, HashMap<String, Scheme>>,
    import_bindings: HashMap<String, String>,
    record_field_callables: HashMap<String, HashMap<String, Vec<ParamCapability>>>,
    known_impl_dicts: HashSet<String>,
    loop_break_tys: Vec<Ty>,
    fn_return_tys: Vec<FuncReturn>,
    pending_constraints: Vec<TraitConstraint>,
    known_impl_schemes: HashMap<String, Scheme>,
    metadata: TypeMetadata,
    current_level: TypeLevel,
}

struct InstantiatedScheme {
    ty: Ty,
    constraints: Vec<TraitConstraint>,
}

#[derive(Debug, Clone)]
struct FinalizedConstraints {
    scheme: Scheme,
    owned: Vec<TraitConstraint>,
    bubbled: Vec<TraitConstraint>,
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

enum DictResolution {
    Resolved(DictRef),
    Pending(PendingDictArg),
}

#[derive(Debug, Clone)]
pub struct InferenceResult {
    pub env: TypeEnv,
    pub variant_env: VariantEnv,
    pub inherent_method_schemes: HashMap<String, HashMap<String, InherentMethodScheme>>,
    pub value_ty: Ty,
    pub expr_types: HashMap<NodeId, Ty>,
    pub symbol_types: HashMap<NodeId, Ty>,
    pub binding_types: HashMap<SourceSpan, Ty>,
    pub definition_schemes: HashMap<SourceSpan, Scheme>,
    pub binding_capabilities: HashMap<SourceSpan, BindingCapabilities>,
    pub callable_capabilities: HashMap<NodeId, CallableCapabilities>,
    pub fresh_place_exprs: HashSet<NodeId>,
}

/// Partial result returned by [`Infer::infer_program_collecting`].
///
/// Diagnostics for individual top-level declarations are reported separately by the caller;
/// this alias carries only the inference state that survived recovery.
///
/// `value_ty` is the trailing-expression type when the trailing expression succeeded, or
/// `Ty::Unit` when the module ends in a declaration or its trailing expression failed.
/// Importing modules should treat `value_ty` of a partial inference as best-effort.
pub type ModuleInference = InferenceResult;

impl Default for InferenceResult {
    fn default() -> Self {
        Self {
            env: TypeEnv::new(),
            variant_env: VariantEnv::default(),
            inherent_method_schemes: HashMap::new(),
            value_ty: Ty::Unit,
            expr_types: HashMap::new(),
            symbol_types: HashMap::new(),
            binding_types: HashMap::new(),
            definition_schemes: HashMap::new(),
            binding_capabilities: HashMap::new(),
            callable_capabilities: HashMap::new(),
            fresh_place_exprs: HashSet::new(),
        }
    }
}

impl Default for Infer {
    fn default() -> Self {
        Self::new()
    }
}

impl Infer {
    pub fn new() -> Self {
        Self {
            subst: Subst::new(),
            trait_env: HashMap::new(),
            variant_env: VariantEnv::default(),
            type_aliases: HashMap::new(),
            declared_types: HashSet::new(),
            scoped_declared_types: HashSet::new(),
            op_trait_map: HashMap::new(),
            inherent_methods: HashMap::new(),
            scoped_inherent_methods: HashMap::new(),
            import_types: HashMap::new(),
            import_schemes: HashMap::new(),
            import_bindings: HashMap::new(),
            record_field_callables: HashMap::new(),
            known_impl_dicts: HashSet::new(),
            loop_break_tys: Vec::new(),
            fn_return_tys: Vec::new(),
            pending_constraints: Vec::new(),
            known_impl_schemes: HashMap::new(),
            metadata: TypeMetadata::default(),
            current_level: ROOT_LEVEL,
        }
    }

    fn fresh_var(&mut self) -> TyVar {
        self.subst.fresh_tyvar_at(self.current_level)
    }

    fn fresh_ty(&mut self) -> Ty {
        Ty::Var(self.fresh_var())
    }

    fn with_child_level<T>(
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

    pub fn set_import_types(&mut self, import_types: HashMap<String, Ty>) {
        self.import_types = import_types;
    }

    pub fn set_import_schemes(&mut self, import_schemes: HashMap<String, HashMap<String, Scheme>>) {
        self.import_schemes = import_schemes;
    }

    pub fn set_known_impl_dicts(&mut self, dicts: HashSet<String>) {
        self.known_impl_dicts = dicts;
    }

    pub fn set_known_impl_schemes(&mut self, schemes: HashMap<String, Scheme>) {
        self.known_impl_schemes = schemes;
    }

    pub fn set_trait_scope(
        &mut self,
        traits: HashMap<String, TraitDef>,
        op_trait_map: HashMap<String, String>,
    ) {
        self.trait_env = traits;
        self.op_trait_map = op_trait_map;
    }

    pub fn set_type_scope(&mut self, type_names: HashSet<String>) {
        self.scoped_declared_types = type_names;
    }

    pub fn set_inherent_scope(
        &mut self,
        inherent_methods: HashMap<String, HashMap<String, InherentMethodScheme>>,
    ) {
        self.scoped_inherent_methods = inherent_methods
            .into_iter()
            .map(|(target, methods)| {
                let dict_name = inherent_impl_dict_name(&target);
                (
                    target,
                    methods
                        .into_iter()
                        .map(|(name, method)| {
                            (
                                name.clone(),
                                InherentMethodInfo {
                                    scheme: method.scheme,
                                    resolved_callee: ResolvedCallee::InherentMethod {
                                        dict: dict_name.clone(),
                                        method: name.clone(),
                                    },
                                    has_receiver: method.has_receiver,
                                },
                            )
                        })
                        .collect(),
                )
            })
            .collect();
    }

    fn instantiate_scheme(&mut self, scheme: &Scheme) -> InstantiatedScheme {
        let mut map = HashMap::new();
        for &v in &scheme.vars {
            map.insert(v, Ty::Var(self.fresh_var()));
        }
        // Only keep constraints whose variable was actually remapped to a fresh Var.
        // If a var somehow mapped to a concrete type, its constraint is already resolved.
        let constraints = scheme
            .constraints
            .iter()
            .filter_map(|c| match map.get(&c.var) {
                Some(Ty::Var(v)) => Some(TraitConstraint {
                    var: *v,
                    trait_name: c.trait_name.clone(),
                    args: c
                        .args
                        .iter()
                        .map(|arg| self.apply_inst(arg, &map))
                        .collect(),
                    determinant_indexes: c.determinant_indexes.clone(),
                }),
                Some(_) => None,
                None => Some(c.clone()),
            })
            .collect();
        InstantiatedScheme {
            ty: self.apply_inst(&scheme.ty, &map),
            constraints,
        }
    }

    fn instantiate(&mut self, scheme: &Scheme) -> Ty {
        self.instantiate_scheme(scheme).ty
    }

    fn instantiate_value(&mut self, scheme: &Scheme) -> Ty {
        let instantiated = self.instantiate_scheme(scheme);
        if instantiated.constraints.is_empty() {
            instantiated.ty
        } else {
            Ty::Qualified(instantiated.constraints, Box::new(instantiated.ty))
        }
    }

    fn imported_member_scheme_for_expr(&self, expr: &Expr) -> Option<Scheme> {
        let ExprKind::FieldAccess {
            expr: base, field, ..
        } = &expr.kind
        else {
            return None;
        };
        self.imported_member_scheme(base, field)
    }

    pub(super) fn imported_member_scheme(&self, base: &Expr, field: &str) -> Option<Scheme> {
        let ExprKind::Ident(base_name) = &base.kind else {
            return None;
        };
        let module_name = self.import_bindings.get(base_name)?;
        self.import_schemes
            .get(module_name)
            .and_then(|members| members.get(field))
            .cloned()
    }

    fn record_symbol_type(&mut self, node_id: NodeId, ty: Ty) {
        self.metadata.record_symbol_type(node_id, ty);
    }

    fn record_callable_capabilities(
        &mut self,
        node_id: NodeId,
        param_capabilities: Vec<ParamCapability>,
    ) {
        self.metadata
            .record_callable_capabilities(node_id, param_capabilities);
    }

    fn callable_capabilities_for(&self, node_id: NodeId) -> Vec<ParamCapability> {
        self.metadata.callable_capabilities_for(node_id)
    }

    fn check_mutable_place_args_from(
        &self,
        env: &TypeEnv,
        args: &[Expr],
        param_capabilities: &[ParamCapability],
        param_offset: usize,
    ) -> Result<(), SpannedTypeError> {
        for (arg_idx, capability) in param_capabilities.iter().enumerate().skip(param_offset) {
            if !capability.is_mut_place() {
                continue;
            }
            let Some(arg) = args.get(arg_idx - param_offset) else {
                continue;
            };
            self.check_mutable_place_arg(env, arg, arg_idx)?;
        }
        Ok(())
    }

    fn check_mutable_place_arg(
        &self,
        env: &TypeEnv,
        arg: &Expr,
        idx: usize,
    ) -> Result<(), SpannedTypeError> {
        if self.is_fresh_mutable_place_expr(arg) {
            return Ok(());
        }
        let Some(name) = find_assignment_base_name(arg) else {
            return Err(TypeError::ExpectedMutablePlace(format!(
                "argument {} must be a mutable place",
                idx + 1
            ))
            .at(arg.span));
        };
        let info = env
            .get(&name)
            .ok_or_else(|| TypeError::UnboundVariable(name.clone()).at(arg.span))?;
        if info.is_place_mutable() {
            Ok(())
        } else {
            Err(TypeError::ExpectedMutablePlace(format!(
                "argument {} must be a mutable place, but `{}` is not mutable",
                idx + 1,
                name
            ))
            .at(arg.span))
        }
    }

    fn record_literal_callable_fields(
        &self,
        value: &Expr,
    ) -> Option<HashMap<String, Vec<ParamCapability>>> {
        let ExprKind::Record(entries) = &value.kind else {
            return None;
        };
        let mut fields = HashMap::new();
        for entry in entries {
            let RecordEntry::Field(name, expr) = entry else {
                continue;
            };
            let Some(capabilities) = self.metadata.callable_capabilities(expr.id) else {
                continue;
            };
            if capabilities
                .param_capabilities
                .iter()
                .any(|cap| cap.is_mut_place())
            {
                fields.insert(name.clone(), capabilities.param_capabilities.clone());
            }
        }
        if fields.is_empty() {
            None
        } else {
            Some(fields)
        }
    }

    fn is_fresh_mutable_place_expr(&self, expr: &Expr) -> bool {
        perf::fresh_place_node();
        if is_fresh_mutable_place(expr) || self.metadata.is_fresh_place_expr(expr.id) {
            return true;
        }
        match &expr.kind {
            ExprKind::Grouped(expr) => self.is_fresh_mutable_place_expr(expr),
            ExprKind::Tuple(exprs) => exprs
                .iter()
                .all(|expr| self.is_fresh_mutable_place_expr(expr)),
            ExprKind::Record(entries) => entries
                .iter()
                .all(|entry| self.is_fresh_mutable_place_expr(entry.expr())),
            ExprKind::Array(entries) => entries
                .iter()
                .all(|entry| self.is_fresh_array_element_place(entry.expr())),
            ExprKind::If {
                then_branch,
                else_branch,
                ..
            } => {
                self.is_fresh_mutable_place_expr(then_branch)
                    && self.is_fresh_mutable_place_expr(else_branch)
            }
            ExprKind::Match { arms, .. } => arms
                .iter()
                .all(|(_, body)| self.is_fresh_mutable_place_expr(body)),
            ExprKind::Block { final_expr, .. } => final_expr
                .as_deref()
                .is_some_and(|expr| self.is_fresh_mutable_place_expr(expr)),
            _ => false,
        }
    }

    fn is_fresh_array_element_place(&self, expr: &Expr) -> bool {
        matches!(expr.kind, ExprKind::Ident(_)) || self.is_fresh_mutable_place_expr(expr)
    }

    fn check_fresh_return_expr(
        &self,
        expr: &Expr,
        ret: &FuncReturn,
    ) -> Result<(), SpannedTypeError> {
        if ret.capability == ReturnCapability::FreshPlace && !self.is_fresh_mutable_place_expr(expr)
        {
            return Err(TypeError::ExpectedMutablePlace(
                "return value must be a fresh mutable place".to_string(),
            )
            .at(expr.span));
        }
        Ok(())
    }

    fn apply_inst(&self, ty: &Ty, map: &HashMap<TyVar, Ty>) -> Ty {
        match ty {
            Ty::Var(v) => map.get(v).cloned().unwrap_or(Ty::Var(*v)),
            Ty::Qualified(constraints, ty) => Ty::Qualified(
                constraints
                    .iter()
                    .filter_map(|c| match map.get(&c.var) {
                        Some(Ty::Var(var)) => Some(TraitConstraint {
                            var: *var,
                            trait_name: c.trait_name.clone(),
                            args: c.args.iter().map(|arg| self.apply_inst(arg, map)).collect(),
                            determinant_indexes: c.determinant_indexes.clone(),
                        }),
                        Some(_) => None,
                        None => Some(c.clone()),
                    })
                    .collect(),
                Box::new(self.apply_inst(ty, map)),
            ),
            Ty::Func(params, ret) => Ty::Func(
                params
                    .iter()
                    .map(|p| FuncParam {
                        ty: self.apply_inst(&p.ty, map),
                        capability: p.capability,
                    })
                    .collect(),
                FuncReturn {
                    ty: Box::new(self.apply_inst(&ret.ty, map)),
                    capability: ret.capability,
                },
            ),
            Ty::Tuple(tys) => Ty::Tuple(tys.iter().map(|t| self.apply_inst(t, map)).collect()),
            Ty::App(con, args) => Ty::App(
                Box::new(self.apply_inst(con, map)),
                args.iter().map(|a| self.apply_inst(a, map)).collect(),
            ),
            Ty::Record(row) => Ty::Record(Row {
                fields: row
                    .fields
                    .iter()
                    .map(|(n, t)| (n.clone(), self.apply_inst(t, map)))
                    .collect(),
                tail: Box::new(self.apply_inst(&row.tail, map)),
            }),
            t => t.clone(),
        }
    }

    fn generalize_at(&self, env: &TypeEnv, ty: Ty, ambient: TypeLevel) -> Scheme {
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

    fn level_generalizable_vars(&self, ty: &Ty, ambient: TypeLevel) -> Vec<TyVar> {
        let mut vars: Vec<_> = free_type_vars(ty)
            .into_iter()
            .filter(|var| self.subst.level_of(*var) > ambient)
            .collect();
        vars.sort();
        vars
    }

    #[cfg(debug_assertions)]
    fn report_level_generalization_shadow(
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
    fn generalizable_vars_by_env_scan(&self, env: &TypeEnv, ty: &Ty) -> Vec<TyVar> {
        let env_vars = env.free_vars(&self.subst);
        let ty_vars = free_type_vars(ty);
        let mut vars: Vec<TyVar> = ty_vars.difference(&env_vars).copied().collect();
        vars.sort();
        vars
    }

    #[cfg(test)]
    fn normalized_free_vars_syntactic(&self, env: &TypeEnv) -> HashSet<TyVar> {
        env.free_vars_syntactic()
            .into_iter()
            .filter_map(|var| match self.subst.apply(&Ty::Var(var)) {
                Ty::Var(resolved) => Some(resolved),
                _ => None,
            })
            .collect()
    }

    fn collect_type_bound_constraints(
        &mut self,
        param_vars: &mut HashMap<String, TyVar>,
        type_bounds: &[TypeBound],
    ) -> Vec<TraitConstraint> {
        let mut constraints = Vec::new();
        for bound in type_bounds {
            let var = if let Some(existing) = param_vars.get(&bound.var) {
                *existing
            } else {
                let fresh = self.fresh_var();
                param_vars.insert(bound.var.clone(), fresh);
                fresh
            };
            for trait_name in &bound.traits {
                constraints.push(TraitConstraint::unary(var, trait_name.clone()));
            }
        }
        constraints
    }

    fn with_pending_constraints_scope<T>(
        &mut self,
        initial_constraints: Vec<TraitConstraint>,
        f: impl FnOnce(&mut Self) -> Result<T, SpannedTypeError>,
    ) -> Result<(T, Vec<TraitConstraint>), SpannedTypeError> {
        let saved_pending = std::mem::take(&mut self.pending_constraints);
        self.pending_constraints.extend(initial_constraints);
        let result = f(self);
        let scoped_pending = std::mem::replace(&mut self.pending_constraints, saved_pending);
        // Failed scopes are discarded wholesale; constraints collected while
        // inferring an invalid body should not leak into the enclosing scope.
        result.map(|value| (value, scoped_pending))
    }

    fn with_fn_return_scope<T>(
        &mut self,
        fn_ret: FuncReturn,
        f: impl FnOnce(&mut Self) -> Result<T, SpannedTypeError>,
    ) -> Result<T, SpannedTypeError> {
        self.fn_return_tys.push(fn_ret);
        let result = f(self);
        self.fn_return_tys.pop();
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
    fn finalize_constraints(
        &self,
        env: &TypeEnv,
        fn_ty: Ty,
        fn_constraints: Vec<TraitConstraint>,
    ) -> FinalizedConstraints {
        self.finalize_constraints_at(env, fn_ty, fn_constraints, self.current_level)
    }

    fn finalize_constraints_at(
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

    // ── Shared Fn/Op inference helper ─────────────────────────────────────────

    /// Infers a function or operator definition, inserting the resulting scheme
    /// into `env`. `add_self_binding` enables recursive calls (set for `fn`,
    /// not for `op`).
    #[allow(clippy::too_many_arguments)]
    fn infer_fn_like(
        &mut self,
        env: &mut TypeEnv,
        name: &str,
        name_span: SourceSpan,
        params: &[Param],
        ret_type: &Option<TypeReturn>,
        body: &mut Expr,
        dict_params: &mut Vec<String>,
        type_bounds: &[TypeBound],
        add_self_binding: bool,
    ) -> Result<(), SpannedTypeError> {
        let ambient = self.current_level;
        let (fn_ty, fn_constraints) = self.with_child_level(|this| {
            let mut param_vars: HashMap<String, TyVar> = HashMap::new();
            let mut param_tys = Vec::new();
            let mut body_env = env.clone();
            let initial_constraints =
                this.collect_type_bound_constraints(&mut param_vars, type_bounds);

            for param in params {
                if !is_irrefutable_param(&param.pat, &this.variant_env) {
                    return Err(TypeError::RefutableParamPattern.at(body.span));
                }
                let p_ty = match &param.ty {
                    Some(t) => this.ast_to_ty_with_vars(t, &mut param_vars)?,
                    None => this.fresh_ty(),
                };
                param_tys.push(p_ty.clone());
                this.check_param_pattern(&param.pat, p_ty, &mut body_env, param.mut_place)?;
            }

            let ret_ty = match ret_type {
                Some(t) => this.ast_to_ty_with_vars(&t.ty, &mut param_vars)?,
                None => this.fresh_ty(),
            };

            let fn_ret = func_return_from_annotation(ret_type, ret_ty.clone());
            let fn_ty = Ty::Func(func_params_from_params(params, param_tys), fn_ret.clone());

            if add_self_binding {
                body_env.insert(
                    name.to_string(),
                    EnvInfo::immutable(Scheme::mono(fn_ty.clone())),
                );
            }

            let (_, fn_constraints) =
                this.with_pending_constraints_scope(initial_constraints, |this| {
                    let body_ty = this.with_fn_return_scope(fn_ret.clone(), |this| {
                        if ret_type.is_some() {
                            this.infer_expr_expected(&body_env, body, ret_ty.clone())
                        } else {
                            this.infer_expr(&body_env, body)
                        }
                    })?;
                    unify_expr_result(&mut this.subst, body_ty.clone(), ret_ty)
                        .map_err(|err| err.at(body.span))?;
                    if !matches!(this.subst.apply(&body_ty), Ty::Never) {
                        this.check_fresh_return_expr(body, &fn_ret)?;
                    }
                    Ok(())
                })?;
            Ok((fn_ty, fn_constraints))
        })?;
        let finalized = self.finalize_constraints_at(env, fn_ty, fn_constraints, ambient);
        self.pending_constraints.extend(finalized.bubbled.clone());

        *dict_params = finalized.owned.iter().map(dict_param_name).collect();

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
        resolve_dict_uses_expr(body, &resolver, false)?;

        env.insert(
            name.to_string(),
            EnvInfo::immutable(finalized.scheme.clone()),
        );
        self.metadata
            .record_definition_scheme(name_span, finalized.scheme);
        Ok(())
    }

    fn apply_env_subst(&self, env: &mut TypeEnv) {
        env.apply_subst(&self.subst);
    }

    fn infer_let_value_ty(
        &mut self,
        env: &TypeEnv,
        ty: &Option<Type>,
        value: &mut Expr,
    ) -> Result<Ty, SpannedTypeError> {
        if let Some(ast_ty) = ty {
            let mut param_vars = HashMap::new();
            let expected_ty = self.ast_to_ty_with_vars(ast_ty, &mut param_vars)?;
            let value_ty = self.infer_expr_expected(env, value, expected_ty.clone())?;
            unify_expr_result(&mut self.subst, value_ty, expected_ty.clone())
                .map_err(|err| err.at(value.span))?;
            Ok(expected_ty)
        } else {
            self.infer_expr(env, value)
        }
    }

    fn finalized_type_maps(&self) -> FinalizedTypeMaps {
        self.metadata.finalize(&self.subst)
    }

    fn record_expr_type_for_node(&mut self, node_id: NodeId, ty: Ty) -> Ty {
        self.metadata.record_expr_type(node_id, ty.clone());
        ty
    }

    pub fn infer_program(&mut self, program: &mut Program) -> Result<TypeEnv, SpannedTypeError> {
        self.infer_program_with_value(program).map(|(env, _)| env)
    }

    pub fn infer_program_with_value(
        &mut self,
        program: &mut Program,
    ) -> Result<(TypeEnv, Ty), SpannedTypeError> {
        self.infer_program_with_seed(program, &[], None)
    }

    pub fn infer_program_with_seed(
        &mut self,
        program: &mut Program,
        seed_stmts: &[Stmt],
        seed_env: Option<&TypeEnv>,
    ) -> Result<(TypeEnv, Ty), SpannedTypeError> {
        self.infer_program_with_seed_and_types(program, seed_stmts, seed_env)
            .map(|result| (result.env, result.value_ty))
    }

    /// Infers types for `program` and returns either a complete result or the first error.
    ///
    /// This is the fail-fast variant. For multi-diagnostic recovery use
    /// [`infer_program_collecting`](Self::infer_program_collecting).
    pub fn infer_program_with_seed_and_types(
        &mut self,
        program: &mut Program,
        seed_stmts: &[Stmt],
        seed_env: Option<&TypeEnv>,
    ) -> Result<InferenceResult, SpannedTypeError> {
        self.reset_program_state();
        self.variant_env = build_variant_env_from_stmts(seed_stmts, &program.stmts);

        let mut env = seed_env.cloned().unwrap_or_else(TypeEnv::new);
        self.validate_type_trait_name_collisions(seed_stmts, &program.stmts)?;
        self.register_type_declarations(seed_stmts.iter().chain(program.stmts.iter()));
        self.register_traits_and_ops(seed_stmts.iter().chain(program.stmts.iter()))?;
        // Fail-fast inference may resolve calls before reaching a later impl statement.
        // Since any failed impl aborts the whole pass, these speculative names cannot
        // leak into a partial result.
        self.register_impl_dict_names(seed_stmts.iter().chain(program.stmts.iter()));

        self.add_constructors_and_externs(&mut env, &mut program.stmts)?;

        let mut value_ty = Ty::Unit;
        for stmt in &mut program.stmts {
            let stmt_ty = self.infer_stmt(&mut env, stmt)?;
            value_ty = match stmt {
                Stmt::Expr(_) => stmt_ty,
                _ => Ty::Unit,
            };
        }

        self.apply_env_subst(&mut env);

        for stmt in &mut program.stmts {
            let resolver = |p: &PendingDictArg| {
                resolve_concrete(
                    p,
                    &env,
                    &self.known_impl_dicts,
                    &self.known_impl_schemes,
                    &self.subst,
                )
            };
            final_pass_stmt(stmt, &resolver)?;
        }

        let maps = self.finalized_type_maps();

        Ok(InferenceResult {
            env,
            variant_env: self.variant_env.clone(),
            inherent_method_schemes: self.export_inherent_method_schemes(),
            value_ty: self.subst.apply(&value_ty),
            expr_types: maps.expr_types,
            symbol_types: maps.symbol_types,
            binding_types: maps.binding_types,
            definition_schemes: maps.definition_schemes,
            binding_capabilities: maps.binding_capabilities,
            callable_capabilities: maps.callable_capabilities,
            fresh_place_exprs: maps.fresh_place_exprs,
        })
    }

    /// Infers types for `program`, collecting diagnostics across multiple top-level
    /// declarations rather than stopping at the first error.
    ///
    /// Recovery model:
    /// - Pre-pass 1 (type aliases) cannot fail.
    /// - Pre-pass 2 (operator-to-trait registry) is fail-fast: a duplicate operator across
    ///   traits would corrupt every later operator inference, so a single accurate
    ///   diagnostic beats partial-recovery noise. The returned `ModuleInference` is empty.
    /// - Pre-pass 3 (constructor types and externs) recovers per declaration: a bad
    ///   payload type or extern signature marks that declaration's bound name unavailable
    ///   without aborting the rest of the pre-pass.
    /// - Main pass: each top-level statement is inferred under a snapshot of the
    ///   substitution map and accumulators. Failure restores the snapshot, marks the
    ///   statement's bound names unavailable, and proceeds. Subsequent statements that
    ///   reference any unavailable name are skipped silently — preventing one root-cause
    ///   error from cascading into a wave of dependent diagnostics.
    /// - Final pass (trait-dictionary resolution) runs only on statements that fully
    ///   succeeded, since restored statements may have stale pending dictionary args.
    pub fn infer_program_collecting(
        &mut self,
        program: &mut Program,
        seed_stmts: &[Stmt],
        seed_env: Option<&TypeEnv>,
    ) -> (ModuleInference, Vec<SpannedTypeError>) {
        self.reset_program_state();
        self.variant_env = build_variant_env_from_stmts(seed_stmts, &program.stmts);

        let mut env = seed_env.cloned().unwrap_or_else(TypeEnv::new);
        if let Err(err) = self.validate_type_trait_name_collisions(seed_stmts, &program.stmts) {
            return (ModuleInference::default(), vec![err]);
        }
        self.register_type_declarations(seed_stmts.iter().chain(program.stmts.iter()));
        if let Err(err) =
            self.register_traits_and_ops(seed_stmts.iter().chain(program.stmts.iter()))
        {
            return (ModuleInference::default(), vec![err]);
        }
        // Collecting inference returns partial state after failures, so current-module
        // impl dictionaries must become visible only after their impl statement succeeds.
        // Module-scope discovery may have preloaded them into `known_impl_dicts`; remove
        // only this program's impl names while preserving imported/prelude impls.
        self.remove_program_impl_dict_names(program.stmts.iter());

        let mut diagnostics: Vec<SpannedTypeError> = Vec::new();
        let mut unavailable = CollectedNames::default();

        // Pre-pass 3: constructor types and externs (per-stmt recovery).
        for stmt in &mut program.stmts {
            let span = stmt.span();
            let bound = stmt_bound_names(stmt);
            match stmt {
                Stmt::Type(td) => {
                    if let Err(err) = self.add_constructors_to_env(&mut env, td) {
                        self.discard_failed_type_decl(td);
                        unavailable.extend(bound);
                        diagnostics.push(err.at(span));
                    }
                }
                Stmt::Extern {
                    name,
                    name_span,
                    ty,
                    ..
                } => {
                    let ambient = self.current_level;
                    match self.with_child_level(|this| {
                        let mut param_vars = HashMap::new();
                        this.ast_to_ty_with_vars(ty, &mut param_vars)
                            .map_err(|err| err.at(span))
                    }) {
                        Ok(t) => {
                            let scheme = self.generalize_at(&env, t, ambient);
                            self.metadata
                                .record_definition_scheme(*name_span, scheme.clone());
                            env.insert(name.clone(), EnvInfo::immutable(scheme));
                        }
                        Err(err) => {
                            unavailable.extend(bound);
                            diagnostics.push(err);
                        }
                    }
                }
                _ => {}
            }
        }

        // Main pass: infer each top-level statement with snapshot/restore on failure.
        let mut value_ty = Ty::Unit;
        let mut succeeded = vec![false; program.stmts.len()];
        for (idx, stmt) in program.stmts.iter_mut().enumerate() {
            let bound = stmt_bound_names(stmt);
            let refs = stmt_referenced_names(stmt);
            if matches!(stmt, Stmt::Type(_) | Stmt::Extern { .. }) && unavailable.overlaps(&bound) {
                continue;
            }
            if unavailable.overlaps(&refs) {
                unavailable.extend(bound);
                continue;
            }

            let snapshot = InferSnapshot::capture(self, &env);

            match self.infer_stmt(&mut env, stmt) {
                Ok(stmt_ty) => {
                    value_ty = if matches!(stmt, Stmt::Expr(_)) {
                        stmt_ty
                    } else {
                        Ty::Unit
                    };
                    snapshot.discard(self);
                    // A successful redefinition shadows any prior failure of the same name.
                    unavailable.remove_all(&bound);
                    succeeded[idx] = true;
                }
                Err(err) => {
                    // Keep metadata discovered in the failed statement for editor features,
                    // but normalize type entries before discarding the statement's substitutions.
                    let failed_metadata = snapshot.metadata_added_before_failure(self);
                    snapshot.restore(self, &mut env);
                    // Keep callee metadata discovered before the error so LSP hover and
                    // signature help can still explain bad calls in a failed statement.
                    self.metadata.extend_failed_statement(failed_metadata);
                    unavailable.extend(bound);
                    diagnostics.push(err);
                }
            }
        }

        self.apply_env_subst(&mut env);

        // Final pass on succeeded statements only — restored statements may carry pending
        // dictionary args that reference type variables from the discarded inference.
        for (stmt, &ok) in program.stmts.iter_mut().zip(succeeded.iter()) {
            if !ok {
                continue;
            }
            let span = stmt.span();
            let resolver = |p: &PendingDictArg| {
                resolve_concrete(
                    p,
                    &env,
                    &self.known_impl_dicts,
                    &self.known_impl_schemes,
                    &self.subst,
                )
            };
            if let Err(err) = final_pass_stmt(stmt, &resolver) {
                diagnostics.push(err.at(span));
            }
        }

        let maps = self.finalized_type_maps();

        (
            ModuleInference {
                env,
                variant_env: self.variant_env.clone(),
                inherent_method_schemes: self.export_inherent_method_schemes(),
                value_ty: self.subst.apply(&value_ty),
                expr_types: maps.expr_types,
                symbol_types: maps.symbol_types,
                binding_types: maps.binding_types,
                definition_schemes: maps.definition_schemes,
                binding_capabilities: maps.binding_capabilities,
                callable_capabilities: maps.callable_capabilities,
                fresh_place_exprs: maps.fresh_place_exprs,
            },
            diagnostics,
        )
    }

    fn reset_program_state(&mut self) {
        self.subst.clear_map_keep_counter();
        self.type_aliases.clear();
        self.declared_types.clear();
        self.declared_types
            .extend(["string", "bool", "int", "float", "Array", "Iter"].map(str::to_string));
        self.declared_types
            .extend(self.scoped_declared_types.iter().cloned());
        self.inherent_methods.clear();
        self.pending_constraints.clear();
        self.loop_break_tys.clear();
        self.fn_return_tys.clear();
        self.metadata.clear();
        self.import_bindings.clear();
        self.record_field_callables.clear();
        self.current_level = ROOT_LEVEL;
    }

    fn infer_stmt(&mut self, env: &mut TypeEnv, stmt: &mut Stmt) -> Result<Ty, SpannedTypeError> {
        let span = stmt.span();
        let result: Result<Ty, SpannedTypeError> = (|| match stmt {
            Stmt::Let {
                pat,
                is_mutable,
                ty,
                value,
                ..
            } => {
                let generalizable_value = !*is_mutable && is_value(&*value);
                let ambient = self.current_level;
                let inferred_ty = if generalizable_value {
                    self.with_child_level(|this| this.infer_let_value_ty(env, ty, value))?
                } else {
                    self.infer_let_value_ty(env, ty, value)?
                };

                // Reject refutable patterns in let position.
                if !is_irrefutable_let(pat, &self.variant_env) {
                    return Err(TypeError::RefutableLetPattern.at(value.span));
                }

                // For a simple variable binding, support let-polymorphism.
                if let Pattern::Variable(name, span) = pat {
                    self.metadata
                        .record_binding_type(*span, inferred_ty.clone());
                    let scheme = if !*is_mutable
                        && ty.is_none()
                        && let Some(imported_scheme) = self.imported_member_scheme_for_expr(value)
                    {
                        imported_scheme
                    } else if !generalizable_value {
                        Scheme::mono(inferred_ty)
                    } else {
                        self.generalize_at(env, inferred_ty, ambient)
                    };
                    let place_mutable = *is_mutable && self.is_fresh_mutable_place_expr(value);
                    self.metadata
                        .record_binding_capability(*span, BindingCapabilities { place_mutable });
                    if let ExprKind::Import(path) = &value.kind {
                        self.import_bindings.insert(name.clone(), path.clone());
                    } else if let Some(fields) = self.record_literal_callable_fields(value) {
                        self.record_field_callables.insert(name.clone(), fields);
                    } else if let ExprKind::Ident(source_name) = &value.kind
                        && let Some(fields) = self.record_field_callables.get(source_name).cloned()
                    {
                        self.record_field_callables.insert(name.clone(), fields);
                    }
                    env.insert(
                        name.clone(),
                        if *is_mutable {
                            EnvInfo::mutable_binding(scheme).with_place_mutable(place_mutable)
                        } else {
                            EnvInfo::immutable(scheme)
                        },
                    );
                } else {
                    // Destructuring: bind each pattern variable, then generalize if
                    // the RHS is a syntactic value (preserving let-polymorphism).
                    //
                    // Snapshot env free vars BEFORE inserting new bindings so that
                    // sibling bindings don't prevent each other from being generalized.
                    let pre_let_env_vars: HashSet<TyVar> = if generalizable_value {
                        env.free_vars(&self.subst)
                    } else {
                        HashSet::new()
                    };
                    self.check_pattern(pat, inferred_ty, env, *is_mutable)?;
                    if generalizable_value {
                        let mut bound = std::collections::HashSet::new();
                        insert_pattern_bindings(&mut bound, pat);
                        let updates: Vec<(String, Ty, bool)> = bound
                            .iter()
                            .filter_map(|name| {
                                env.get(name).map(|info| {
                                    (name.clone(), info.scheme.ty.clone(), info.binding_mutable)
                                })
                            })
                            .collect();
                        for (name, ty, is_mut) in updates {
                            let applied = self.subst.apply(&ty);
                            let mut ty_vars = HashSet::new();
                            free_type_vars_into(&applied, &mut ty_vars);
                            let mut vars: Vec<TyVar> =
                                ty_vars.difference(&pre_let_env_vars).copied().collect();
                            vars.sort();
                            let scheme = Scheme {
                                vars,
                                constraints: vec![],
                                ty: applied,
                            };
                            env.insert(
                                name,
                                if is_mut {
                                    EnvInfo::mutable_binding(scheme)
                                } else {
                                    EnvInfo::immutable(scheme)
                                },
                            );
                        }
                    }
                }
                Ok(Ty::Unit)
            }
            Stmt::Fn {
                name,
                name_span,
                params,
                ret_type,
                body,
                dict_params,
                type_bounds,
                ..
            } => {
                self.infer_fn_like(
                    env,
                    name,
                    *name_span,
                    params,
                    ret_type,
                    body,
                    dict_params,
                    type_bounds,
                    true,
                )?;
                Ok(Ty::Unit)
            }
            Stmt::Op {
                name,
                name_span,
                params,
                ret_type,
                body,
                dict_params,
                type_bounds,
                ..
            } => {
                self.infer_fn_like(
                    env,
                    name,
                    *name_span,
                    params,
                    ret_type,
                    body,
                    dict_params,
                    type_bounds,
                    false,
                )?;
                Ok(Ty::Unit)
            }
            Stmt::Type(_) | Stmt::TypeAlias { .. } | Stmt::Extern { .. } => Ok(Ty::Unit),
            Stmt::Trait(_) => Ok(Ty::Unit),
            Stmt::Impl(id) => {
                self.infer_impl(env, id)?;
                Ok(Ty::Unit)
            }
            Stmt::InherentImpl(id) => {
                self.infer_inherent_impl(env, id)?;
                Ok(Ty::Unit)
            }
            Stmt::Expr(expr) => self.infer_expr(env, expr),
        })();
        result.map_err(|err| err.with_span_if_absent(span))
    }

    fn infer_expr_expected(
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
                body,
                dict_params,
            } => {
                if let Ty::Func(expected_params, expected_ret) = expected.clone() {
                    let ty = self.infer_lambda_expr(
                        env,
                        expr_id,
                        params,
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

    fn infer_expr(&mut self, env: &TypeEnv, expr: &mut Expr) -> Result<Ty, SpannedTypeError> {
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
            ExprKind::Unit => Ok(Ty::Unit),
            ExprKind::Import(path) => self
                .import_types
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
                self.loop_break_tys.push(break_ty.clone());
                let _body_ty = self.infer_expr(env, body)?;
                self.loop_break_tys.pop();
                Ok(break_ty)
            }
            ExprKind::Break(val) => {
                let break_ty = self
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
                if self.loop_break_tys.is_empty() {
                    Err(TypeError::ContinueOutsideLoop.into())
                } else {
                    Ok(Ty::Never)
                }
            }
            ExprKind::Return(val) => {
                let ret = self
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
                        self.record_field_callables
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
                body,
                dict_params,
            } => self.infer_lambda_expr(env, expr_id, params, body, dict_params, None),
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

    #[allow(clippy::too_many_arguments)]
    fn infer_index_expr(
        &mut self,
        env: &TypeEnv,
        receiver: &mut Expr,
        key: &mut Expr,
        resolved_callee: &mut Option<ResolvedCallee>,
        pending_trait_method: &mut Option<(PendingDictArg, String)>,
        _dict_args: &mut Vec<DictRef>,
        _pending_dict_args: &mut Vec<PendingDictArg>,
    ) -> Result<Ty, SpannedTypeError> {
        let trait_def = self
            .trait_env
            .get("Index")
            .ok_or_else(|| TypeError::UnknownTrait("Index".to_string()))?
            .clone();
        if trait_def.params.len() != INDEX_TRAIT_ARITY {
            return Err(TypeError::TraitArityMismatch {
                trait_name: "Index".to_string(),
                expected: INDEX_TRAIT_ARITY,
                got: trait_def.params.len(),
            }
            .into());
        }
        let receiver_ty = self.infer_expr(env, receiver)?;
        let key_ty = self.infer_expr(env, key)?;
        let output_ty = Ty::Var(self.fresh_var());
        let args = [receiver_ty.clone(), key_ty.clone(), output_ty.clone()];
        let determinant_indexes = trait_dict_indexes(&trait_def);

        let resolved_args: Vec<Ty> = args.iter().map(|arg| self.subst.apply(arg)).collect();
        if let Some(output_ty) = self.resolve_multi_param_trait_dispatch(
            env,
            "Index",
            "index",
            resolved_args,
            determinant_indexes,
            vec![receiver_ty, key_ty],
            output_ty.clone(),
            resolved_callee,
            pending_trait_method,
            "Index dictionaries should be concrete",
        )? {
            return Ok(output_ty);
        }

        Err(TypeError::MissingTraitImpl {
            trait_name: "Index".to_string(),
            impl_target: format!(
                "{}, {}",
                self.subst.apply(&args[0]),
                self.subst.apply(&args[1])
            ),
        }
        .into())
    }

    fn infer_range_expr(
        &mut self,
        env: &TypeEnv,
        start: Option<&mut Expr>,
        end: Option<&mut Expr>,
        inclusive: bool,
    ) -> Result<Ty, SpannedTypeError> {
        let int_ty = Ty::Int;
        match (start, end, inclusive) {
            (Some(start), Some(end), false) => {
                let start_ty = self.infer_expr(env, start)?;
                unify(&mut self.subst, start_ty, int_ty.clone()).map_err(|err| {
                    err.with_mismatch_context(TypeMismatchContext::RangeStart)
                        .at(start.span)
                })?;
                let end_ty = self.infer_expr(env, end)?;
                unify(&mut self.subst, end_ty, int_ty.clone()).map_err(|err| {
                    err.with_mismatch_context(TypeMismatchContext::RangeEnd)
                        .at(end.span)
                })?;
                Ok(range_ty("Range"))
            }
            (Some(start), Some(end), true) => {
                let start_ty = self.infer_expr(env, start)?;
                unify(&mut self.subst, start_ty, int_ty.clone()).map_err(|err| {
                    err.with_mismatch_context(TypeMismatchContext::RangeStart)
                        .at(start.span)
                })?;
                let end_ty = self.infer_expr(env, end)?;
                unify(&mut self.subst, end_ty, int_ty.clone()).map_err(|err| {
                    err.with_mismatch_context(TypeMismatchContext::RangeEnd)
                        .at(end.span)
                })?;
                Ok(range_ty("RangeInclusive"))
            }
            (Some(start), None, false) => {
                let start_ty = self.infer_expr(env, start)?;
                unify(&mut self.subst, start_ty, int_ty).map_err(|err| {
                    err.with_mismatch_context(TypeMismatchContext::RangeStart)
                        .at(start.span)
                })?;
                Ok(range_ty("RangeFrom"))
            }
            (Some(_), None, true) => {
                unreachable!("parser rejects inclusive ranges without end bounds")
            }
            (None, Some(end), false) => {
                let end_ty = self.infer_expr(env, end)?;
                unify(&mut self.subst, end_ty, int_ty).map_err(|err| {
                    err.with_mismatch_context(TypeMismatchContext::RangeEnd)
                        .at(end.span)
                })?;
                Ok(range_ty("RangeTo"))
            }
            (None, Some(end), true) => {
                let end_ty = self.infer_expr(env, end)?;
                unify(&mut self.subst, end_ty, int_ty).map_err(|err| {
                    err.with_mismatch_context(TypeMismatchContext::RangeEnd)
                        .at(end.span)
                })?;
                Ok(range_ty("RangeToInclusive"))
            }
            (None, None, false) => Ok(Ty::Con("RangeFull".to_string())),
            (None, None, true) => {
                unreachable!("parser rejects inclusive ranges without end bounds")
            }
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn infer_binary_expr(
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

    fn infer_pipe_expr(
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

    #[allow(clippy::too_many_arguments)]
    fn infer_custom_binary_expr(
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
        if let Some(trait_name) = self.op_trait_map.get(op).cloned() {
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
    fn infer_trait_operator_expr(
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
            .trait_env
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

        let mut param_vars: HashMap<String, TyVar> = HashMap::new();
        let target_var = self.fresh_var();
        let trait_param = primary_param_or_panic(&trait_def);
        param_vars.insert(trait_param.to_string(), target_var);

        let lhs_param_ty = self.ast_to_ty_with_vars(&method.params[0].1, &mut param_vars)?;
        let rhs_param_ty = self.ast_to_ty_with_vars(&method.params[1].1, &mut param_vars)?;
        let ret_ty = self.ast_to_ty_with_vars(&method.ret_type, &mut param_vars)?;

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
        Ok(self.subst.apply(&ret_ty))
    }

    #[allow(clippy::too_many_arguments)]
    fn infer_function_operator_expr(
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

    #[allow(clippy::too_many_arguments)]
    fn infer_call_expr(
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
                        Err(_) => return Err(trait_err),
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

        if let ExprKind::Ident(method_name) = &callee.kind
            && env.get(method_name.as_str()).is_none()
            && let Some(resolved) = self.bare_trait_method(method_name)?
        {
            return self.resolve_trait_method_call(
                env,
                args,
                arg_wrappers,
                resolved_callee,
                pending_trait_method,
                resolved.trait_def,
                resolved.method,
                "bare trait method call",
            );
        }

        if let ExprKind::Ident(callee_name) = &callee.kind
            && let Some(info) = env.get(callee_name.as_str())
        {
            let scheme = info.scheme.clone();
            if !scheme.constraints.is_empty() {
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
                    0,
                    dict_args,
                    pending_dict_args,
                )?;
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

    fn infer_record_expr(
        &mut self,
        env: &TypeEnv,
        entries: &mut [RecordEntry],
        span: SourceSpan,
    ) -> Result<Ty, SpannedTypeError> {
        let mut field_tys: Vec<(String, Ty)> = Vec::new();
        let mut tail = Ty::Unit;
        for entry in entries {
            match entry {
                RecordEntry::Field(name, expr) => {
                    let ty = self.infer_expr(env, expr)?;
                    merge_record_field(&mut field_tys, name.clone(), ty);
                }
                RecordEntry::Spread(expr) => {
                    let spread_ty = self.infer_expr(env, expr)?;
                    let tail_var = self.fresh_ty();
                    unify(
                        &mut self.subst,
                        spread_ty.clone(),
                        Ty::Record(Row {
                            fields: vec![],
                            tail: Box::new(tail_var),
                        }),
                    )?;
                    let resolved_spread = self.subst.apply(&spread_ty);
                    let Ty::Record(row) = resolved_spread else {
                        return Err(TypeError::Mismatch(
                            Ty::Record(Row {
                                fields: vec![],
                                tail: Box::new(self.fresh_ty()),
                            }),
                            resolved_spread,
                        )
                        .at(span));
                    };
                    for (name, ty) in row.fields {
                        merge_record_field(&mut field_tys, name, ty);
                    }
                    tail = merge_record_spread_tail(&mut self.subst, tail, *row.tail)
                        .map_err(|err| err.at(span))?;
                }
            }
        }
        field_tys.sort_by(|(a, _), (b, _)| a.cmp(b));
        Ok(Ty::Record(Row {
            fields: field_tys,
            tail: Box::new(tail),
        }))
    }

    fn infer_for_expr(
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
            .trait_env
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
            Ty::App(_, args) if args.len() == 1 => args.into_iter().next().unwrap(), // len == 1 from pattern guard
            other => other,
        };

        let mut body_env = env.clone();
        let elem_ty_applied = self.subst.apply(&elem_ty);
        self.check_pattern(pat, elem_ty_applied, &mut body_env, false)?;

        self.loop_break_tys.push(Ty::Unit);
        self.infer_expr(&body_env, body)?;
        self.loop_break_tys.pop();

        Ok(Ty::Unit)
    }

    fn resolve_iterable_dict(
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
                    self.pending_constraints
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
                env.get(dict_name).is_some() || self.known_impl_dicts.contains(dict_name)
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

    fn infer_array_entries(
        &mut self,
        env: &TypeEnv,
        entries: &mut [ArrayEntry],
        expected: Option<Ty>,
        span: SourceSpan,
    ) -> Result<Ty, SpannedTypeError> {
        let expected_element = expected.as_ref().and_then(array_element_ty);
        let elt_ty = expected_element.clone().unwrap_or_else(|| self.fresh_ty());
        for entry in entries {
            match entry {
                ArrayEntry::Elem(expr) => {
                    let ty = if expected_element.is_some() {
                        self.infer_expr_expected(env, expr, elt_ty.clone())?
                    } else {
                        self.infer_expr(env, expr)?
                    };
                    unify(&mut self.subst, elt_ty.clone(), ty)?;
                }
                ArrayEntry::Spread(expr) => {
                    let expected_array =
                        Ty::App(Box::new(Ty::Con("Array".to_string())), vec![elt_ty.clone()]);
                    let ty = if expected_element.is_some() {
                        self.infer_expr_expected(env, expr, expected_array.clone())?
                    } else {
                        self.infer_expr(env, expr)?
                    };
                    unify(&mut self.subst, ty, expected_array)?;
                }
            }
        }
        let array_ty = Ty::App(Box::new(Ty::Con("Array".to_string())), vec![elt_ty]);
        if let Some(expected) = expected {
            unify(&mut self.subst, array_ty.clone(), expected).map_err(|err| err.at(span))?;
        }
        Ok(self.subst.apply(&array_ty))
    }

    #[allow(clippy::too_many_arguments)]
    fn infer_lambda_expr(
        &mut self,
        env: &TypeEnv,
        expr_id: NodeId,
        params: &[Param],
        body: &mut Expr,
        dict_params: &mut Vec<String>,
        expected_func: Option<(Vec<FuncParam>, FuncReturn)>,
    ) -> Result<Ty, SpannedTypeError> {
        let ambient = self.current_level;
        let (fn_ty, fn_constraints) = self.with_child_level(|this| {
            let mut param_vars: HashMap<String, TyVar> = HashMap::new();
            let mut param_tys = Vec::new();
            let mut body_env = env.clone();

            if let Some((expected_params, _)) = &expected_func
                && expected_params.len() != params.len()
            {
                return Err(TypeError::ArityMismatch {
                    expected: expected_params.len(),
                    got: params.len(),
                }
                .at(body.span));
            }

            for (idx, param) in params.iter().enumerate() {
                if !is_irrefutable_param(&param.pat, &this.variant_env) {
                    return Err(TypeError::RefutableParamPattern.at(body.span));
                }
                let expected_param = expected_func
                    .as_ref()
                    .and_then(|(expected_params, _)| expected_params.get(idx));
                if let Some(expected_param) = expected_param
                    && expected_param.capability.is_mut_place() != param.mut_place
                {
                    return Err(TypeError::MutableFunctionCapabilityMismatch.at(body.span));
                }
                let p_ty = match (&param.ty, expected_param) {
                    (Some(t), Some(expected_param)) => {
                        let annotated = this.ast_to_ty_with_vars(t, &mut param_vars)?;
                        unify(
                            &mut this.subst,
                            annotated.clone(),
                            expected_param.ty.clone(),
                        )
                        .map_err(|err| err.at(body.span))?;
                        annotated
                    }
                    (Some(t), None) => this.ast_to_ty_with_vars(t, &mut param_vars)?,
                    (None, Some(expected_param)) => expected_param.ty.clone(),
                    (None, None) => this.fresh_ty(),
                };
                param_tys.push(p_ty.clone());
                this.check_param_pattern(&param.pat, p_ty, &mut body_env, param.mut_place)?;
            }

            let (ret_ty, ret_capability) = match &expected_func {
                Some((_, expected_ret)) => ((*expected_ret.ty).clone(), expected_ret.capability),
                None => (this.fresh_ty(), ReturnCapability::Value),
            };
            let fn_ret = FuncReturn {
                ty: Box::new(ret_ty.clone()),
                capability: ret_capability,
            };
            let (_, fn_constraints) = this.with_pending_constraints_scope(Vec::new(), |this| {
                let body_ty = this.with_fn_return_scope(fn_ret.clone(), |this| {
                    if expected_func.is_some() {
                        this.infer_expr_expected(&body_env, body, ret_ty.clone())
                    } else {
                        this.infer_expr(&body_env, body)
                    }
                })?;
                unify_expr_result(&mut this.subst, body_ty.clone(), ret_ty.clone())?;
                if !matches!(this.subst.apply(&body_ty), Ty::Never) {
                    this.check_fresh_return_expr(body, &fn_ret)?;
                }
                Ok(())
            })?;

            let fn_ty = Ty::Func(
                func_params_from_params(params, param_tys),
                FuncReturn {
                    ty: Box::new(this.subst.apply(&ret_ty)),
                    capability: ret_capability,
                },
            );
            Ok((fn_ty, fn_constraints))
        })?;
        let finalized = self.finalize_constraints_at(env, fn_ty, fn_constraints, ambient);
        self.pending_constraints.extend(finalized.bubbled.clone());
        *dict_params = finalized.owned.iter().map(dict_param_name).collect();

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
        resolve_dict_uses_expr_lenient(body, &resolver, false)?;

        self.record_callable_capabilities(expr_id, param_capabilities(params));

        Ok(if finalized.owned.is_empty() {
            finalized.scheme.ty
        } else {
            Ty::Qualified(finalized.owned, Box::new(finalized.scheme.ty))
        })
    }

    fn check_pattern(
        &mut self,
        pat: &Pattern,
        scrutinee_ty: Ty,
        env: &mut TypeEnv,
        binding_mutable: bool,
    ) -> Result<(), TypeError> {
        let binding_info = |scheme| {
            if binding_mutable {
                EnvInfo::mutable_binding(scheme)
            } else {
                EnvInfo::immutable(scheme)
            }
        };
        match pat {
            Pattern::Wildcard => Ok(()),
            Pattern::StringLit(_) => {
                unify(&mut self.subst, scrutinee_ty, Ty::Con("string".to_string()))
            }
            Pattern::Variable(name, span) => {
                self.metadata
                    .record_binding_type(*span, scrutinee_ty.clone());
                env.insert(name.clone(), binding_info(Scheme::mono(scrutinee_ty)));
                Ok(())
            }
            Pattern::Constructor { name, binding } => {
                let info = self
                    .variant_env
                    .0
                    .get(name)
                    .ok_or_else(|| TypeError::UnboundVariable(name.clone()))?
                    .clone();

                let mut param_map: HashMap<String, TyVar> = HashMap::new();
                let type_args: Vec<Ty> = info
                    .type_params
                    .iter()
                    .map(|p| {
                        let v = self.fresh_var();
                        param_map.insert(p.clone(), v);
                        Ty::Var(v)
                    })
                    .collect();

                let con_ty = if type_args.is_empty() {
                    Ty::Con(info.type_name.clone())
                } else {
                    Ty::App(Box::new(Ty::Con(info.type_name.clone())), type_args)
                };
                unify(&mut self.subst, scrutinee_ty, con_ty)?;

                if let Some(binding) = binding {
                    let payload_ty = match &info.payload {
                        Some(ast_ty) => self.ast_to_ty_with_vars(ast_ty, &mut param_map)?,
                        None => {
                            return Err(TypeError::UnboundVariable(format!(
                                "variant `{}` has no payload to bind",
                                name
                            )));
                        }
                    };
                    self.check_pattern(binding, payload_ty, env, binding_mutable)?;
                }
                Ok(())
            }
            Pattern::Record { fields, rest } => {
                let tail_var = self.fresh_var();
                let tail = if rest.is_some() {
                    Ty::Var(tail_var)
                } else {
                    Ty::Unit
                };

                // Build sorted field-type pairs for unification.
                let mut field_tys: Vec<(String, Ty)> = fields
                    .iter()
                    .map(|(field_name, _, _)| (field_name.clone(), self.fresh_ty()))
                    .collect();
                field_tys.sort_by(|(a, _), (b, _)| a.cmp(b));

                unify(
                    &mut self.subst,
                    scrutinee_ty,
                    Ty::Record(Row {
                        fields: field_tys.clone(),
                        tail: Box::new(tail),
                    }),
                )?;

                // Bind each field's type to its binding name by looking up the field name
                // in the (sorted) field_tys rather than relying on positional zip.
                for (field_name, binding_name, binding_span) in fields.iter() {
                    if binding_name == "_" {
                        continue;
                    }
                    if let Some((_, field_ty)) = field_tys.iter().find(|(n, _)| n == field_name) {
                        self.metadata
                            .record_binding_type(*binding_span, self.subst.apply(field_ty));
                        env.insert(
                            binding_name.clone(),
                            binding_info(Scheme::mono(self.subst.apply(field_ty))),
                        );
                    }
                }

                if let Some(Some((rest_name, rest_span))) = rest {
                    let rest_ty = self.subst.apply(&Ty::Var(tail_var));
                    self.metadata
                        .record_binding_type(*rest_span, rest_ty.clone());
                    env.insert(rest_name.clone(), binding_info(Scheme::mono(rest_ty)));
                }
                Ok(())
            }
            Pattern::List { elements, rest } => {
                let elt_ty = self.fresh_ty();
                let arr_ty = Ty::App(Box::new(Ty::Con("Array".to_string())), vec![elt_ty.clone()]);
                unify(&mut self.subst, scrutinee_ty, arr_ty.clone())?;

                for elem in elements {
                    self.check_pattern(elem, elt_ty.clone(), env, binding_mutable)?;
                }
                if let Some(Some((rest_name, rest_span))) = rest {
                    self.metadata
                        .record_binding_type(*rest_span, arr_ty.clone());
                    env.insert(rest_name.clone(), binding_info(Scheme::mono(arr_ty)));
                }
                Ok(())
            }
            Pattern::Tuple(pats) => {
                let elem_tys: Vec<Ty> = pats.iter().map(|_| self.fresh_ty()).collect();
                unify(&mut self.subst, scrutinee_ty, Ty::Tuple(elem_tys.clone()))?;
                for (p, t) in pats.iter().zip(elem_tys.iter()) {
                    let resolved = self.subst.apply(t);
                    self.check_pattern(p, resolved, env, binding_mutable)?;
                }
                Ok(())
            }
        }
    }

    fn check_param_pattern(
        &mut self,
        pat: &Pattern,
        scrutinee_ty: Ty,
        env: &mut TypeEnv,
        mut_place: bool,
    ) -> Result<(), TypeError> {
        if !mut_place {
            return self.check_pattern(pat, scrutinee_ty, env, false);
        }
        let Pattern::Variable(name, span) = pat else {
            return Err(TypeError::MutableParamMustBindName);
        };
        self.metadata
            .record_binding_type(*span, scrutinee_ty.clone());
        self.metadata.record_binding_capability(
            *span,
            BindingCapabilities {
                place_mutable: true,
            },
        );
        env.insert(
            name.clone(),
            EnvInfo::immutable(Scheme::mono(scrutinee_ty)).with_place_mutable(true),
        );
        Ok(())
    }

    fn check_exhaustive(
        &self,
        arms: &[(Pattern, Expr)],
        scrutinee_ty: &Ty,
    ) -> Result<(), TypeError> {
        let patterns: Vec<&Pattern> = arms.iter().map(|(p, _)| p).collect();
        check_exhaustive_match(&patterns, scrutinee_ty, &self.variant_env)
    }

    fn ast_to_ty_with_vars(
        &mut self,
        ast_ty: &Type,
        param_vars: &mut HashMap<String, TyVar>,
    ) -> Result<Ty, TypeError> {
        self.ast_to_ty_with_vars_inner(ast_ty, param_vars, &mut Vec::new())
    }

    fn ast_to_ty_with_vars_inner(
        &mut self,
        ast_ty: &Type,
        param_vars: &mut HashMap<String, TyVar>,
        alias_stack: &mut Vec<String>,
    ) -> Result<Ty, TypeError> {
        Ok(match ast_ty {
            Type::Ident(name) => {
                if let Some((params, aliased_ty)) = self.type_aliases.get(name).cloned() {
                    if !params.is_empty() {
                        return Err(TypeError::TypeAliasArityMismatch {
                            name: name.clone(),
                            expected: params.len(),
                            got: 0,
                        });
                    }
                    return self.expand_type_alias(name, &aliased_ty, param_vars, alias_stack);
                }
                match name.as_str() {
                    "int" => Ty::Int,
                    "float" => Ty::Float,
                    "Unit" | "()" => Ty::Unit,
                    _ if self.declared_types.contains(name) => Ty::Con(name.clone()),
                    _ => return Err(TypeError::UnknownType(name.clone())),
                }
            }
            Type::Never => Ty::Never,
            Type::Var(name) => {
                if let Some(&v) = param_vars.get(name) {
                    Ty::Var(v)
                } else {
                    let v = self.fresh_var();
                    param_vars.insert(name.clone(), v);
                    Ty::Var(v)
                }
            }
            Type::Func(params, ret) => {
                let param_tys = params
                    .iter()
                    .map(|p| {
                        self.ast_to_ty_with_vars_inner(&p.ty, param_vars, alias_stack)
                            .map(|ty| {
                                if p.mut_place {
                                    FuncParam::mut_place(ty)
                                } else {
                                    FuncParam::value(ty)
                                }
                            })
                    })
                    .collect::<Result<_, _>>()?;
                Ty::Func(
                    param_tys,
                    if ret.mut_place {
                        FuncReturn::fresh_place(self.ast_to_ty_with_vars_inner(
                            &ret.ty,
                            param_vars,
                            alias_stack,
                        )?)
                    } else {
                        value_func_return(self.ast_to_ty_with_vars_inner(
                            &ret.ty,
                            param_vars,
                            alias_stack,
                        )?)
                    },
                )
            }
            Type::App(con, args) => {
                if let Type::Ident(name) = &**con
                    && let Some((params, aliased_ty)) = self.type_aliases.get(name).cloned()
                {
                    if params.len() != args.len() {
                        return Err(TypeError::TypeAliasArityMismatch {
                            name: name.clone(),
                            expected: params.len(),
                            got: args.len(),
                        });
                    }
                    let mut substituted = aliased_ty;
                    for (param, arg) in params.iter().zip(args.iter()) {
                        substituted = subst_hkt_param(&substituted, param, arg);
                    }
                    return self.expand_type_alias(name, &substituted, param_vars, alias_stack);
                }
                let con_ty = self.ast_to_ty_with_vars_inner(con, param_vars, alias_stack)?;
                let arg_tys = args
                    .iter()
                    .map(|a| self.ast_to_ty_with_vars_inner(a, param_vars, alias_stack))
                    .collect::<Result<_, _>>()?;
                Ty::App(Box::new(con_ty), arg_tys)
            }
            Type::Tuple(tys) => Ty::Tuple(
                tys.iter()
                    .map(|t| self.ast_to_ty_with_vars_inner(t, param_vars, alias_stack))
                    .collect::<Result<_, _>>()?,
            ),
            Type::Record(fields, is_open) => {
                let mut field_tys: Vec<_> = fields
                    .iter()
                    .map(|(n, t)| {
                        self.ast_to_ty_with_vars_inner(t, param_vars, alias_stack)
                            .map(|ty| (n.clone(), ty))
                    })
                    .collect::<Result<_, _>>()?;
                field_tys.sort_by(|(a, _), (b, _)| a.cmp(b));
                let tail = if *is_open { self.fresh_ty() } else { Ty::Unit };
                Ty::Record(Row {
                    fields: field_tys,
                    tail: Box::new(tail),
                })
            }
            Type::Unit => Ty::Unit,
            Type::Hole => self.fresh_ty(),
        })
    }

    fn expand_type_alias(
        &mut self,
        name: &str,
        aliased_ty: &Type,
        param_vars: &mut HashMap<String, TyVar>,
        alias_stack: &mut Vec<String>,
    ) -> Result<Ty, TypeError> {
        if alias_stack.iter().any(|alias| alias == name) {
            return Err(TypeError::RecursiveTypeAlias(name.to_string()));
        }

        alias_stack.push(name.to_string());
        let result = self.ast_to_ty_with_vars_inner(aliased_ty, param_vars, alias_stack);
        alias_stack.pop();
        result
    }
}

fn param_capabilities(params: &[Param]) -> Vec<ParamCapability> {
    params
        .iter()
        .map(|param| {
            if param.mut_place {
                ParamCapability::MutPlace
            } else {
                ParamCapability::Value
            }
        })
        .collect()
}

fn func_params_from_params(params: &[Param], param_tys: Vec<Ty>) -> Vec<FuncParam> {
    params
        .iter()
        .zip(param_tys)
        .map(|(param, ty)| {
            if param.mut_place {
                FuncParam::mut_place(ty)
            } else {
                FuncParam::value(ty)
            }
        })
        .collect()
}

fn func_return_from_annotation(ret_type: &Option<TypeReturn>, ret_ty: Ty) -> FuncReturn {
    if ret_type.as_ref().is_some_and(|ret| ret.mut_place) {
        FuncReturn::fresh_place(ret_ty)
    } else {
        value_func_return(ret_ty)
    }
}

fn combine_branch_types(subst: &mut Subst, left: Ty, right: Ty) -> Result<Ty, TypeError> {
    let left = subst.apply(&left);
    let right = subst.apply(&right);
    match (&left, &right) {
        _ if is_never(&left) && is_never(&right) => Ok(Ty::Never),
        _ if is_never(&left) => Ok(right),
        _ if is_never(&right) => Ok(left),
        _ => {
            unify(subst, left.clone(), right)?;
            Ok(subst.apply(&left))
        }
    }
}

fn unify_expr_result(subst: &mut Subst, actual: Ty, expected: Ty) -> Result<(), TypeError> {
    if is_never(&subst.apply(&actual)) {
        return Ok(());
    }
    unify(subst, actual, expected)
}

fn constructor_pattern_refinement_mismatch(
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

    TypeError::Mismatch(scrutinee_after_pattern, scrutinee_before_pattern).at(span)
}

fn is_never(ty: &Ty) -> bool {
    matches!(ty, Ty::Never)
}

fn range_ty(name: &str) -> Ty {
    Ty::App(Box::new(Ty::Con(name.to_string())), vec![Ty::Int])
}

fn merge_record_field(fields: &mut Vec<(String, Ty)>, name: String, ty: Ty) {
    if let Some(pos) = fields.iter().position(|(existing, _)| existing == &name) {
        fields[pos].1 = ty;
    } else {
        fields.push((name, ty));
    }
}

fn merge_record_spread_tail(subst: &mut Subst, existing: Ty, next: Ty) -> Result<Ty, TypeError> {
    let existing = subst.apply(&existing);
    let next = subst.apply(&next);
    match (existing, next) {
        (Ty::Unit, tail) | (tail, Ty::Unit) => Ok(tail),
        (Ty::Var(left), Ty::Var(right)) if left == right => Ok(Ty::Var(left)),
        (left, right) => {
            unify(subst, left.clone(), right)?;
            Ok(subst.apply(&left))
        }
    }
}

fn array_element_ty(ty: &Ty) -> Option<Ty> {
    match ty {
        Ty::App(con, args)
            if matches!(con.as_ref(), Ty::Con(name) if name == "Array") && args.len() == 1 =>
        {
            Some(args[0].clone())
        }
        _ => None,
    }
}

fn func_param_capabilities(params: &[FuncParam]) -> Vec<ParamCapability> {
    params.iter().map(|param| param.capability).collect()
}

fn func_return_capability(ty: &Ty) -> ReturnCapability {
    match ty {
        Ty::Func(_, ret) => ret.capability,
        _ => ReturnCapability::Value,
    }
}

fn scheme_param_capabilities(scheme: &Scheme) -> Vec<ParamCapability> {
    match &scheme.ty {
        Ty::Func(params, _) => func_param_capabilities(params),
        _ => Vec::new(),
    }
}

fn scheme_param_capability(scheme: &Scheme, idx: usize) -> ParamCapability {
    scheme_param_capabilities(scheme)
        .get(idx)
        .copied()
        .unwrap_or(ParamCapability::Value)
}

fn expected_func_params(callee_ty: &Ty, arg_tys: Vec<Ty>) -> Vec<FuncParam> {
    match callee_ty {
        Ty::Func(params, _) if params.len() == arg_tys.len() => params
            .iter()
            .zip(arg_tys)
            .map(|(param, ty)| FuncParam {
                ty,
                capability: param.capability,
            })
            .collect(),
        _ => value_func_params(arg_tys),
    }
}

fn expected_func_return(callee_ty: &Ty, ret_ty: Ty) -> FuncReturn {
    match callee_ty {
        Ty::Func(_, ret) => FuncReturn {
            ty: Box::new(ret_ty),
            capability: ret.capability,
        },
        _ => value_func_return(ret_ty),
    }
}

fn has_mut_place_func_params(ty: &Ty) -> bool {
    matches!(ty, Ty::Func(params, _) if params.iter().any(|param| param.capability.is_mut_place()))
}

fn is_unknown_trait_method_error(err: &SpannedTypeError) -> bool {
    matches!(err.error.as_ref(), TypeError::UnknownTraitMethod { .. })
}

pub(super) fn primary_param_or_panic(trait_def: &TraitDef) -> &str {
    trait_def
        .primary_param()
        .expect("parser rejects zero-parameter traits")
}

fn primary_trait_var(args: &[Ty], determinant_indexes: &[usize]) -> Option<TyVar> {
    // Pending dictionary parameters are named by the first unresolved determinant.
    // Other determinants remain in the full predicate and are checked again when
    // final-pass dictionary resolution has more substitution information.
    determinant_indexes
        .iter()
        .filter_map(|index| args.get(*index))
        .find_map(first_ty_var)
        .or_else(|| args.iter().find_map(first_ty_var))
}

fn first_ty_var(ty: &Ty) -> Option<TyVar> {
    match ty {
        Ty::Var(var) => Some(*var),
        Ty::Qualified(constraints, inner) => first_ty_var(inner).or_else(|| {
            constraints
                .iter()
                .flat_map(|constraint| constraint.args.iter())
                .find_map(first_ty_var)
        }),
        Ty::Tuple(items) => items.iter().find_map(first_ty_var),
        Ty::Func(params, ret) => params
            .iter()
            .find_map(|param| first_ty_var(&param.ty))
            .or_else(|| first_ty_var(&ret.ty)),
        // Prefer the constructor first so HKT-shaped targets like `'f('a)` dispatch on `'f`.
        Ty::App(con, args) => first_ty_var(con).or_else(|| args.iter().find_map(first_ty_var)),
        Ty::Record(row) => row
            .fields
            .iter()
            .find_map(|(_, ty)| first_ty_var(ty))
            .or_else(|| first_ty_var(&row.tail)),
        Ty::Int | Ty::Float | Ty::Unit | Ty::Never | Ty::Con(_) => None,
    }
}

/// Returns true if the AST `Type` mentions `var_name` as a type variable.
/// Used to decide whether a trait method's first parameter contains the HKT
/// trait parameter (e.g. `'f` in `'f('a)`), which determines the dispatch
/// strategy in `resolve_trait_method_call`.
fn type_contains_var(ty: &Type, var_name: &str) -> bool {
    match ty {
        Type::Var(name) => name == var_name,
        Type::App(con, args) => {
            type_contains_var(con, var_name) || args.iter().any(|a| type_contains_var(a, var_name))
        }
        Type::Func(params, ret) => {
            params.iter().any(|p| type_contains_var(&p.ty, var_name))
                || type_contains_var(&ret.ty, var_name)
        }
        Type::Tuple(tys) => tys.iter().any(|t| type_contains_var(t, var_name)),
        Type::Record(fields, _) => fields.iter().any(|(_, t)| type_contains_var(t, var_name)),
        Type::Ident(_) | Type::Unit | Type::Never | Type::Hole => false,
    }
}

fn find_assignment_base_name(expr: &Expr) -> Option<String> {
    match &expr.kind {
        ExprKind::Grouped(expr) => find_assignment_base_name(expr),
        ExprKind::FieldAccess { expr, .. } => find_assignment_base_name(expr),
        ExprKind::Ident(name) => Some(name.clone()),
        _ => None,
    }
}

fn expr_always_exits(expr: &Expr, include_bc: bool) -> bool {
    match &expr.kind {
        ExprKind::Return(_) => true,
        ExprKind::Break(_) | ExprKind::Continue => include_bc,
        ExprKind::Grouped(e) | ExprKind::Not(e) | ExprKind::FieldAccess { expr: e, .. } => {
            expr_always_exits(e, include_bc)
        }
        ExprKind::Binary { lhs, rhs, .. } => {
            expr_always_exits(lhs, include_bc) || expr_always_exits(rhs, include_bc)
        }
        ExprKind::Assign { target, value } => {
            expr_always_exits(target, include_bc) || expr_always_exits(value, include_bc)
        }
        ExprKind::Call { callee, args, .. } => {
            expr_always_exits(callee, include_bc)
                || args.iter().any(|arg| expr_always_exits(arg, include_bc))
        }
        ExprKind::Tuple(es) => es.iter().any(|expr| expr_always_exits(expr, include_bc)),
        ExprKind::Array(entries) => entries
            .iter()
            .any(|entry| expr_always_exits(entry.expr(), include_bc)),
        ExprKind::Record(entries) => entries
            .iter()
            .any(|entry| expr_always_exits(entry.expr(), include_bc)),
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            expr_always_exits(cond, include_bc)
                || expr_always_exits(then_branch, include_bc)
                    && expr_always_exits(else_branch, include_bc)
        }
        ExprKind::Match { scrutinee, arms } => {
            expr_always_exits(scrutinee, include_bc)
                || !arms.is_empty()
                    && arms
                        .iter()
                        .all(|(_, body)| expr_always_exits(body, include_bc))
        }
        ExprKind::Block { stmts, final_expr } => {
            for stmt in stmts {
                if stmt_always_exits(stmt, include_bc) {
                    return true;
                }
            }
            final_expr
                .as_ref()
                .is_some_and(|expr| expr_always_exits(expr, include_bc))
        }
        ExprKind::Loop(body) => expr_always_exits(body, false),
        ExprKind::For { iterable, .. } => expr_always_exits(iterable, include_bc),
        ExprKind::Import(_) => false,
        _ => false,
    }
}

fn stmt_always_exits(stmt: &Stmt, include_bc: bool) -> bool {
    match stmt {
        Stmt::Expr(expr) | Stmt::Let { value: expr, .. } => expr_always_exits(expr, include_bc),
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::pipeline::{parse_source, reassociate_standalone};

    #[test]
    fn failed_type_declaration_prunes_variant_state() {
        let mut program = parse_source("type Broken('a) = Good('a) | Bad(Missing)\n")
            .expect("source should parse");
        reassociate_standalone(&mut program);

        let mut infer = Infer::new();
        let (inference, diagnostics) = infer.infer_program_collecting(&mut program, &[], None);

        assert_eq!(diagnostics.len(), 1);
        assert_eq!(diagnostics[0].span.expect("type error span").start_line, 1);
        assert!(!infer.declared_types.contains("Broken"));
        assert!(!infer.variant_env.0.contains_key("Good"));
        assert!(!infer.variant_env.0.contains_key("Bad"));
        assert!(inference.env.get("Good").is_none());
        assert!(inference.env.get("Bad").is_none());
    }

    #[test]
    fn collecting_inference_skips_nested_pattern_references_to_unavailable_variants() {
        let mut program = parse_source(
            "type Broken('a) = Good('a) | Bad(Missing)\n\
             fn dependent(xs) { match xs { [(Good(x), y)] -> x, _ -> 0 } }\n\
             let other: bool = 1;\n",
        )
        .expect("source should parse");
        reassociate_standalone(&mut program);

        let mut infer = Infer::new();
        let (inference, diagnostics) = infer.infer_program_collecting(&mut program, &[], None);

        assert_eq!(
            diagnostics.len(),
            2,
            "dependent nested pattern should be skipped, not diagnosed again"
        );
        assert_eq!(
            diagnostics
                .iter()
                .map(|diagnostic| diagnostic.span.expect("type error span").start_line)
                .collect::<Vec<_>>(),
            vec![1, 3]
        );
        assert!(inference.env.get("dependent").is_none());
        assert!(inference.env.get("other").is_none());
    }

    #[test]
    fn collecting_inference_normalizes_failed_symbol_types_before_rollback() {
        let mut program = parse_source(
            "fn takes(x) { x }\n\
             if takes(1) { 0 } else { 1 }\n",
        )
        .expect("source should parse");
        reassociate_standalone(&mut program);

        let callee_id = match &program.stmts[1] {
            Stmt::Expr(expr) => match &expr.kind {
                ExprKind::If { cond, .. } => match &cond.kind {
                    ExprKind::Call { callee, .. } => callee.id,
                    _ => panic!("condition should be a call"),
                },
                _ => panic!("second statement should be an if expression"),
            },
            _ => panic!("second statement should be an expression"),
        };

        let mut infer = Infer::new();
        let (inference, diagnostics) = infer.infer_program_collecting(&mut program, &[], None);

        assert_eq!(diagnostics.len(), 1);
        let callee_ty = inference
            .symbol_types
            .get(&callee_id)
            .expect("failed call callee type should be retained");
        assert!(
            free_type_vars(callee_ty).is_empty(),
            "retained failed symbol type should be normalized, got {callee_ty}"
        );
        match callee_ty {
            Ty::Func(params, ret) => {
                assert_eq!(params.len(), 1);
                assert_eq!(params[0].ty, Ty::Int);
                assert_eq!(*ret.ty, Ty::Int);
            }
            other => panic!("callee should retain a function type, got {other}"),
        }
    }

    #[test]
    fn same_name_single_constructor_type_is_nominal() {
        let mut program = parse_source(
            "type Wrap = Wrap(float)\n\
             impl Wrap {\n\
               fn unwrap(self) { match self { Wrap(value) -> value } }\n\
             }\n\
             let wrapped = Wrap(1.0);\n\
             let value = wrapped.unwrap();\n",
        )
        .expect("source should parse");
        reassociate_standalone(&mut program);

        assert!(matches!(
            &program.stmts[0],
            Stmt::Type(td) if td.name == "Wrap" && td.variants.len() == 1
        ));

        let mut infer = Infer::new();
        infer
            .infer_program(&mut program)
            .expect("same-name constructor should infer as a nominal type");
    }

    #[test]
    fn recursive_type_alias_reports_error_instead_of_recursing() {
        let mut program = parse_source(
            "type A = B\n\
             type B = A\n\
             extern value: A = \"value\";\n",
        )
        .expect("source should parse");
        reassociate_standalone(&mut program);

        let mut infer = Infer::new();
        let err = infer
            .infer_program(&mut program)
            .expect_err("recursive aliases should be rejected");

        assert!(matches!(
            err.error.as_ref(),
            TypeError::RecursiveTypeAlias(_)
        ));
    }

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
            .pending_constraints
            .push(TraitConstraint::unary(0, "Outer".to_string()));

        let err = infer
            .with_pending_constraints_scope(
                vec![TraitConstraint::unary(1, "Inner".to_string())],
                |this| {
                    this.pending_constraints
                        .push(TraitConstraint::unary(2, "Body".to_string()));
                    Err::<(), SpannedTypeError>(TypeError::UnknownType("boom".to_string()).into())
                },
            )
            .expect_err("scope body should fail");

        assert!(matches!(err.error.as_ref(), TypeError::UnknownType(_)));
        assert_eq!(
            infer.pending_constraints,
            vec![TraitConstraint::unary(0, "Outer".to_string())]
        );

        let err = infer
            .with_fn_return_scope(value_func_return(Ty::Int), |_this| {
                Err::<(), SpannedTypeError>(TypeError::UnknownType("return".to_string()).into())
            })
            .expect_err("return scope body should fail");
        assert!(matches!(err.error.as_ref(), TypeError::UnknownType(_)));
        assert!(infer.fn_return_tys.is_empty());
    }

    #[test]
    fn collecting_inference_does_not_mutate_failed_inherent_self_types() {
        let mut program = parse_source(
            "type Box = Box(int)\n\
             impl Box {\n\
               fn bad(self, other: Self) -> int { true }\n\
             }\n",
        )
        .expect("source should parse");
        reassociate_standalone(&mut program);

        let mut infer = Infer::new();
        let (_inference, diagnostics) = infer.infer_program_collecting(&mut program, &[], None);

        assert_eq!(diagnostics.len(), 1);
        let Stmt::InherentImpl(id) = &program.stmts[1] else {
            panic!("second statement should be an inherent impl");
        };
        let Some(Type::Ident(name)) = id.methods[0].params[1].ty.as_ref() else {
            panic!("failed inherent impl method should retain its original Self annotation");
        };
        assert_eq!(name, "Self");
    }

    #[test]
    fn collecting_inference_does_not_partially_mutate_failed_inherent_impl() {
        let mut program = parse_source(
            "type Box = Box(int)\n\
             impl Box {\n\
               fn ok(self, other: Self) -> int { 1 }\n\
               fn bad(self, other: Self) -> int { true }\n\
             }\n",
        )
        .expect("source should parse");
        reassociate_standalone(&mut program);

        let mut infer = Infer::new();
        let (_inference, diagnostics) = infer.infer_program_collecting(&mut program, &[], None);

        assert_eq!(diagnostics.len(), 1);
        let Stmt::InherentImpl(id) = &program.stmts[1] else {
            panic!("second statement should be an inherent impl");
        };
        for method in &id.methods {
            let Some(Type::Ident(name)) = method.params[1].ty.as_ref() else {
                panic!("failed inherent impl should retain original Self annotations");
            };
            assert_eq!(name, "Self");
        }
    }

    #[test]
    fn missing_primitive_trait_impl_is_rejected_during_inference() {
        let err = infer_source_error(
            "trait Show 'a {
               fn show(x: 'a) -> string
             }

             show(1)\n",
        );

        assert!(matches!(
            err.error.as_ref(),
            TypeError::MissingTraitImpl {
                trait_name,
                impl_target,
            } if trait_name == "Show" && impl_target == "int"
        ));
    }

    #[test]
    fn missing_custom_type_trait_impl_is_rejected_during_inference() {
        let err = infer_source_error(
            "type Boxed = Boxed(float)

             trait Show 'a {
               fn show(x: 'a) -> string
             }

             show(Boxed(1.0))\n",
        );

        assert!(matches!(
            err.error.as_ref(),
            TypeError::MissingTraitImpl {
                trait_name,
                impl_target,
            } if trait_name == "Show" && impl_target == "Boxed"
        ));
    }

    #[test]
    fn collecting_inference_does_not_use_failed_local_impl_dict() {
        let mut program = parse_source(
            "type Boxed = Boxed(float)

             trait Show 'a {
               fn show(x: 'a) -> string
             }

             impl Show for Boxed {
               fn show(x) { 1 }
             }

             show(Boxed(1.0))\n",
        )
        .expect("source should parse");

        let mut infer = Infer::new();
        let (_inference, diagnostics) = infer.infer_program_collecting(&mut program, &[], None);

        assert!(diagnostics.iter().any(|diagnostic| {
            matches!(
                diagnostic.error.as_ref(),
                TypeError::MissingTraitImpl {
                    trait_name,
                    impl_target,
                } if trait_name == "Show" && impl_target == "Boxed"
            )
        }));
    }

    #[test]
    fn missing_structural_tuple_component_impl_is_rejected_during_inference() {
        let err = infer_source_error(
            "type Boxed = Boxed(float)

             trait Eq 'a {
               fn infix 4 ==(lhs: 'a, rhs: 'a) -> bool
               fn infix 4 !=(lhs: 'a, rhs: 'a) -> bool
             }

             impl Eq for float {
               fn ==(lhs, rhs) { true }
               fn !=(lhs, rhs) { false }
             }

             fn bad(a: (Boxed, float), b: (Boxed, float)) -> bool {
               a == b
             }\n",
        );

        assert!(matches!(
            err.error.as_ref(),
            TypeError::MissingTraitImpl {
                trait_name,
                impl_target,
            } if trait_name == "Eq" && impl_target == "Boxed"
        ));
    }

    #[test]
    fn available_concrete_trait_impl_resolves_to_checked_dict_ref() {
        let mut program = parse_source(
            "trait Show 'a {
               fn show(x: 'a) -> string
             }

             impl Show for float {
               fn show(x) { \"ok\" }
             }

             show(1.0)\n",
        )
        .expect("source should parse");
        reassociate_standalone(&mut program);

        let mut infer = Infer::new();
        infer
            .infer_program(&mut program)
            .expect("available concrete impl should infer");

        let Stmt::Expr(expr) = &program.stmts[2] else {
            panic!("third statement should be the call expression");
        };
        let ExprKind::Call {
            dict_args,
            pending_dict_args,
            resolved_callee,
            ..
        } = &expr.kind
        else {
            panic!("third statement should be a call");
        };

        assert!(pending_dict_args.is_empty());
        assert!(dict_args.is_empty());
        match resolved_callee {
            Some(ResolvedCallee::DictMethod {
                dict: DictRef::Concrete(name),
                method,
            }) => {
                assert_eq!(name, "__Show__float");
                assert_eq!(method, "show");
            }
            other => panic!("expected concrete checked dict method, got {other:?}"),
        }
    }

    #[test]
    fn legacy_qualified_trait_method_dot_syntax_is_not_trait_dispatch() {
        let err = infer_source_error(
            "trait Show 'a {
               fn show(x: 'a) -> string
             }

             impl Show for float {
               fn show(x) { \"ok\" }
             }

             Show.show(1.0)\n",
        );

        assert!(matches!(err.error.as_ref(), TypeError::UnboundVariable(name) if name == "Show"));
    }

    #[test]
    fn qualified_trait_method_colon_colon_syntax_dispatches_trait_method() {
        let mut program = parse_source(
            "trait Show 'a {
               fn show(x: 'a) -> string
             }

             impl Show for float {
               fn show(x) { \"ok\" }
             }

             Show::show(1.0)\n",
        )
        .expect("source should parse");
        reassociate_standalone(&mut program);

        Infer::new()
            .infer_program(&mut program)
            .expect("qualified trait method should infer");
    }

    fn infer_source_error(source: &str) -> SpannedTypeError {
        let mut program = parse_source(source).expect("source should parse");
        reassociate_standalone(&mut program);

        Infer::new()
            .infer_program(&mut program)
            .expect_err("source should fail inference")
    }
}
