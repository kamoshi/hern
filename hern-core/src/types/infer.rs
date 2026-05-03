use crate::ast::*;
use crate::codegen::lua::mangle_op;
use crate::types::{
    EnvInfo, Row, Scheme, Subst, TraitConstraint, Ty, TyVar,
    error::{SpannedTypeError, TypeError},
    free_type_vars, unify,
};
use std::collections::{HashMap, HashSet};
use std::fmt;

impl fmt::Display for EnvInfo {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let prefix = if self.is_mutable { "mut " } else { "" };
        write!(f, "{}{}", prefix, self.scheme)
    }
}

impl fmt::Display for TypeEnv {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut keys: Vec<_> = self.0.keys().collect();
        keys.sort();
        for key in keys {
            writeln!(f, "  {}: {}", key, self.0.get(key).unwrap())?; // keys from self.0.keys()
        }
        Ok(())
    }
}

// ── Type environment ──────────────────────────────────────────────────────────

#[derive(Debug, Clone, Default)]
pub struct TypeEnv(pub HashMap<String, EnvInfo>);

impl TypeEnv {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn insert(&mut self, name: String, info: EnvInfo) {
        self.0.insert(name, info);
    }

    pub fn get(&self, name: &str) -> Option<&EnvInfo> {
        self.0.get(name)
    }

    fn free_vars(&self, s: &Subst) -> HashSet<TyVar> {
        let mut vars = HashSet::new();
        for info in self.0.values() {
            vars.extend(free_type_vars(&s.apply_scheme(&info.scheme).ty));
        }
        vars
    }

    fn free_vars_syntactic(&self) -> HashSet<TyVar> {
        let mut vars = HashSet::new();
        for info in self.0.values() {
            let mut scheme_vars = free_type_vars(&info.scheme.ty);
            for constraint in &info.scheme.constraints {
                scheme_vars.insert(constraint.var);
            }
            for quantified in &info.scheme.vars {
                scheme_vars.remove(quantified);
            }
            vars.extend(scheme_vars);
        }
        vars
    }
}

struct ResolvedTraitMethod {
    trait_def: TraitDef,
    method: TraitMethod,
}

// ── Variant environment ───────────────────────────────────────────────────────

#[derive(Debug, Clone)]
pub struct VariantInfo {
    pub type_name: String,
    pub type_params: Vec<String>,
    pub type_param_vars: Vec<TyVar>,
    pub payload: Option<Type>,
    pub payload_ty: Option<Ty>,
}

#[derive(Debug, Clone, Default)]
pub struct VariantEnv(pub HashMap<String, VariantInfo>);

fn build_variant_env_from_stmts(seed_stmts: &[Stmt], stmts: &[Stmt]) -> VariantEnv {
    let mut env = VariantEnv::default();
    for stmt in seed_stmts.iter().chain(stmts.iter()) {
        if let Stmt::Type(td) = stmt {
            for variant in &td.variants {
                env.0.insert(
                    variant.name.clone(),
                    VariantInfo {
                        type_name: td.name.clone(),
                        type_params: td.params.clone(),
                        type_param_vars: Vec::new(),
                        payload: variant.payload.clone(),
                        payload_ty: None,
                    },
                );
            }
        }
    }
    env
}

// ── Value predicate ───────────────────────────────────────────────────────────

pub fn is_value(expr: &Expr) -> bool {
    match &expr.kind {
        ExprKind::Number(_)
        | ExprKind::StringLit(_)
        | ExprKind::Bool(_)
        | ExprKind::Ident(_)
        | ExprKind::Lambda { .. }
        | ExprKind::Import(_)
        | ExprKind::Unit => true,
        ExprKind::Tuple(exprs) => exprs.iter().all(is_value),
        ExprKind::Array(entries) => entries.iter().all(|e| is_value(e.expr())),
        ExprKind::Record(entries) => entries.iter().all(|e| is_value(e.expr())),
        _ => false,
    }
}

// ── Infer ─────────────────────────────────────────────────────────────────────

pub struct Infer {
    subst: Subst,
    trait_env: HashMap<String, TraitDef>,
    variant_env: VariantEnv,
    type_aliases: HashMap<String, (Vec<String>, Type)>,
    declared_types: HashSet<String>,
    op_trait_map: HashMap<String, String>,
    import_types: HashMap<String, Ty>,
    known_impl_dicts: HashSet<String>,
    loop_break_tys: Vec<Ty>,
    fn_return_tys: Vec<Ty>,
    pending_constraints: Vec<TraitConstraint>,
    expr_types: HashMap<NodeId, Ty>,
    symbol_types: HashMap<NodeId, Ty>,
    binding_types: HashMap<SourceSpan, Ty>,
    definition_schemes: HashMap<SourceSpan, Scheme>,
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

#[derive(Debug, Clone)]
pub struct InferenceResult {
    pub env: TypeEnv,
    pub variant_env: VariantEnv,
    pub value_ty: Ty,
    pub expr_types: HashMap<NodeId, Ty>,
    pub symbol_types: HashMap<NodeId, Ty>,
    pub binding_types: HashMap<SourceSpan, Ty>,
    pub definition_schemes: HashMap<SourceSpan, Scheme>,
}

/// Partial result returned by [`Infer::infer_program_collecting`].
///
/// Diagnostics for individual top-level declarations are reported separately by the caller;
/// this struct carries only the inference state that survived recovery.
///
/// `value_ty` is the trailing-expression type when the trailing expression succeeded, or
/// `Ty::Unit` when the module ends in a declaration or its trailing expression failed.
/// Importing modules should treat `value_ty` of a partial inference as best-effort.
#[derive(Debug, Clone)]
pub struct ModuleInference {
    pub env: TypeEnv,
    pub variant_env: VariantEnv,
    pub value_ty: Ty,
    pub expr_types: HashMap<NodeId, Ty>,
    pub symbol_types: HashMap<NodeId, Ty>,
    pub binding_types: HashMap<SourceSpan, Ty>,
    pub definition_schemes: HashMap<SourceSpan, Scheme>,
}

impl Default for ModuleInference {
    fn default() -> Self {
        Self {
            env: TypeEnv::new(),
            variant_env: VariantEnv::default(),
            value_ty: Ty::Unit,
            expr_types: HashMap::new(),
            symbol_types: HashMap::new(),
            binding_types: HashMap::new(),
            definition_schemes: HashMap::new(),
        }
    }
}

/// Snapshot of mutable per-statement state inside [`Infer`], taken before each top-level
/// statement during collecting inference. On statement failure the snapshot is restored so
/// the next statement starts from a clean baseline.
///
/// Note: only the substitution **map** is snapshotted, not `Subst::next_var`. Fresh type
/// variable IDs keep advancing across recovery — reusing IDs from a failed statement could
/// alias new bindings against stale references and silently miscompile.
///
/// `variant_env` is intentionally omitted here: it is finalized before the main recovery loop,
/// and failed type declarations are pruned from it during pre-pass 3, so later statements never
/// observe variants from declarations whose constructor environment was discarded.
struct InferSnapshot {
    subst_map: HashMap<TyVar, Ty>,
    pending_constraints: Vec<TraitConstraint>,
    loop_break_tys: Vec<Ty>,
    fn_return_tys: Vec<Ty>,
    expr_types: HashMap<NodeId, Ty>,
    symbol_types: HashMap<NodeId, Ty>,
    binding_types: HashMap<SourceSpan, Ty>,
    definition_schemes: HashMap<SourceSpan, Scheme>,
    env: TypeEnv,
}

/// Top-level names tracked for recovery decisions.
///
/// Value and type namespaces are kept separate so a failed type declaration does not suppress an
/// unrelated value with the same spelling, and vice versa.
#[derive(Debug, Clone, Default)]
struct CollectedNames {
    values: HashSet<String>,
    types: HashSet<String>,
}

impl CollectedNames {
    fn extend(&mut self, other: Self) {
        self.values.extend(other.values);
        self.types.extend(other.types);
    }

    fn overlaps(&self, other: &Self) -> bool {
        self.values.iter().any(|name| other.values.contains(name))
            || self.types.iter().any(|name| other.types.contains(name))
    }

    fn remove_all(&mut self, other: &Self) {
        self.values.retain(|name| !other.values.contains(name));
        self.types.retain(|name| !other.types.contains(name));
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
            op_trait_map: HashMap::new(),
            import_types: HashMap::new(),
            known_impl_dicts: HashSet::new(),
            loop_break_tys: Vec::new(),
            fn_return_tys: Vec::new(),
            pending_constraints: Vec::new(),
            expr_types: HashMap::new(),
            symbol_types: HashMap::new(),
            binding_types: HashMap::new(),
            definition_schemes: HashMap::new(),
        }
    }

    fn fresh_var(&mut self) -> TyVar {
        self.subst.fresh_tyvar()
    }

    pub fn set_import_types(&mut self, import_types: HashMap<String, Ty>) {
        self.import_types = import_types;
    }

    pub fn set_known_impl_dicts(&mut self, dicts: HashSet<String>) {
        self.known_impl_dicts = dicts;
    }

    pub fn set_trait_scope(
        &mut self,
        traits: HashMap<String, TraitDef>,
        op_trait_map: HashMap<String, String>,
    ) {
        self.trait_env = traits;
        self.op_trait_map = op_trait_map;
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
                        }),
                        Some(_) => None,
                        None => Some(c.clone()),
                    })
                    .collect(),
                Box::new(self.apply_inst(ty, map)),
            ),
            Ty::Func(params, ret) => Ty::Func(
                params.iter().map(|p| self.apply_inst(p, map)).collect(),
                Box::new(self.apply_inst(ret, map)),
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

    fn generalize(&self, env: &TypeEnv, ty: Ty) -> Scheme {
        let ty = self.subst.apply(&ty);
        let env_vars = env.free_vars(&self.subst);
        let ty_vars = free_type_vars(&ty);
        let mut vars: Vec<TyVar> = ty_vars.difference(&env_vars).copied().collect();
        vars.sort();
        // Constraints are set separately by finalize_constraints for Fn/Op.
        // For other uses (constructors, externs, let-values) there are no constraints.
        Scheme {
            vars,
            constraints: vec![],
            ty,
        }
    }

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
                constraints.push(TraitConstraint {
                    var,
                    trait_name: trait_name.clone(),
                });
            }
        }
        constraints
    }

    fn finalize_constraints(
        &self,
        env: &TypeEnv,
        fn_ty: Ty,
        fn_constraints: Vec<TraitConstraint>,
    ) -> FinalizedConstraints {
        let mut scheme = self.generalize(env, fn_ty);
        let env_vars = self.normalized_free_vars_syntactic(env);
        let mut seen = HashSet::new();
        let mut seen_bubbled = HashSet::new();
        let mut owned = Vec::new();
        let mut bubbled = Vec::new();

        for constraint in fn_constraints {
            match self.subst.apply(&Ty::Var(constraint.var)) {
                Ty::Var(var) => {
                    let normalized = TraitConstraint {
                        var,
                        trait_name: constraint.trait_name,
                    };
                    if env_vars.contains(&normalized.var) || !scheme.vars.contains(&normalized.var)
                    {
                        if seen_bubbled.insert(normalized.clone()) {
                            bubbled.push(normalized);
                        }
                    } else if seen.insert(normalized.clone()) {
                        owned.push(normalized);
                    }
                }
                // Concrete constraints do not become callable dictionary
                // parameters. Their pending dict uses are resolved by the
                // local/concrete resolver after inference has finished.
                _ => {}
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
        params: &[(Pattern, Option<Type>)],
        ret_type: &Option<Type>,
        body: &mut Expr,
        dict_params: &mut Vec<String>,
        type_bounds: &[TypeBound],
        add_self_binding: bool,
    ) -> Result<(), SpannedTypeError> {
        let mut param_vars: HashMap<String, TyVar> = HashMap::new();
        let mut param_tys = Vec::new();
        let mut body_env = env.clone();
        let initial_constraints = self.collect_type_bound_constraints(&mut param_vars, type_bounds);

        for (pat, p_type) in params {
            if !is_irrefutable_param(pat) {
                return Err(TypeError::RefutableParamPattern.at(body.span));
            }
            let p_ty = match p_type {
                Some(t) => self.ast_to_ty_with_vars(t, &mut param_vars)?,
                None => self.subst.fresh_var(),
            };
            param_tys.push(p_ty.clone());
            self.check_pattern(pat, p_ty, &mut body_env, false)?;
        }

        let ret_ty = match ret_type {
            Some(t) => self.ast_to_ty_with_vars(t, &mut param_vars)?,
            None => self.subst.fresh_var(),
        };

        let fn_ty = Ty::Func(param_tys, Box::new(ret_ty.clone()));

        let saved_pending = std::mem::take(&mut self.pending_constraints);
        self.pending_constraints.extend(initial_constraints);

        if add_self_binding {
            body_env.insert(
                name.to_string(),
                EnvInfo {
                    scheme: Scheme::mono(fn_ty.clone()),
                    is_mutable: false,
                },
            );
        }

        self.fn_return_tys.push(ret_ty.clone());
        let body_ty = self.infer_expr(&body_env, body)?;
        self.fn_return_tys.pop();
        unify(&mut self.subst, body_ty, ret_ty).map_err(|err| err.at(body.span))?;

        let fn_constraints = std::mem::replace(&mut self.pending_constraints, saved_pending);
        let finalized = self.finalize_constraints(env, fn_ty, fn_constraints);
        self.pending_constraints.extend(finalized.bubbled.clone());

        *dict_params = finalized.owned.iter().map(dict_param_name).collect();

        let resolver =
            |p: &PendingDictArg| resolve_local_or_concrete(p, &finalized.owned, &self.subst);
        resolve_dict_uses_expr(body, &resolver, false)?;

        env.insert(
            name.to_string(),
            EnvInfo {
                scheme: finalized.scheme.clone(),
                is_mutable: false,
            },
        );
        self.definition_schemes.insert(name_span, finalized.scheme);
        Ok(())
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

        // Pre-pass 1: type aliases
        for stmt in seed_stmts.iter().chain(program.stmts.iter()) {
            match stmt {
                Stmt::Type(td) => {
                    self.declared_types.insert(td.name.clone());
                }
                Stmt::TypeAlias {
                    name, params, ty, ..
                } => {
                    self.declared_types.insert(name.clone());
                    self.type_aliases
                        .insert(name.clone(), (params.clone(), ty.clone()));
                }
                _ => {}
            }
        }
        self.resolve_variant_payload_types();

        // Pre-pass 2: operator-to-trait registry
        for stmt in seed_stmts.iter().chain(program.stmts.iter()) {
            if let Stmt::Trait(td) = stmt {
                validate_trait_methods_have_target(td)?;
                self.trait_env.insert(td.name.clone(), td.clone());
                for method in &td.methods {
                    if method.fixity.is_some() {
                        if let Some(existing) = self.op_trait_map.get(&method.name) {
                            if existing != &td.name {
                                return Err(TypeError::DuplicateOperator(method.name.clone())
                                    .at(stmt.span()));
                            }
                        } else {
                            self.op_trait_map
                                .insert(method.name.clone(), td.name.clone());
                        }
                    }
                }
            }
        }
        // Seed this program's own impl dictionaries for standalone inference. Graph
        // inference also calls set_known_impl_dicts with the full module env; the
        // overlap is harmless and keeps both entry points on the same call path.
        self.register_impl_dict_names(seed_stmts.iter().chain(program.stmts.iter()));

        // Pre-pass 3: constructor types and externs
        for stmt in &mut program.stmts {
            let span = stmt.span();
            match stmt {
                Stmt::Type(td) => self
                    .add_constructors_to_env(&mut env, td)
                    .map_err(|err| err.at(span))?,
                Stmt::Extern {
                    name,
                    name_span,
                    ty,
                    ..
                } => {
                    let mut param_vars = HashMap::new();
                    let t = self
                        .ast_to_ty_with_vars(ty, &mut param_vars)
                        .map_err(|err| err.at(span))?;
                    let scheme = self.generalize(&env, t);
                    self.definition_schemes.insert(*name_span, scheme.clone());
                    env.insert(
                        name.clone(),
                        EnvInfo {
                            scheme,
                            is_mutable: false,
                        },
                    );
                }
                _ => {}
            }
        }

        let mut value_ty = Ty::Unit;
        for stmt in &mut program.stmts {
            let stmt_ty = self.infer_stmt(&mut env, stmt)?;
            value_ty = match stmt {
                Stmt::Expr(_) => stmt_ty,
                _ => Ty::Unit,
            };
        }

        for info in env.0.values_mut() {
            info.scheme.ty = self.subst.apply(&info.scheme.ty);
        }

        for stmt in &mut program.stmts {
            let resolver = |p: &PendingDictArg| resolve_concrete(p, &self.subst);
            final_pass_stmt(stmt, &resolver)?;
        }

        let expr_types = self
            .expr_types
            .iter()
            .map(|(id, ty)| (*id, self.subst.apply(ty)))
            .collect();
        let symbol_types = self
            .symbol_types
            .iter()
            .map(|(id, ty)| (*id, self.subst.apply(ty)))
            .collect();
        let binding_types = self
            .binding_types
            .iter()
            .map(|(span, ty)| (*span, self.subst.apply(ty)))
            .collect();
        let definition_schemes = self
            .definition_schemes
            .iter()
            .map(|(span, scheme)| (*span, self.subst.apply_scheme(scheme)))
            .collect();

        Ok(InferenceResult {
            env,
            variant_env: self.variant_env.clone(),
            value_ty: self.subst.apply(&value_ty),
            expr_types,
            symbol_types,
            binding_types,
            definition_schemes,
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

        // Pre-pass 1: type aliases (infallible).
        for stmt in seed_stmts.iter().chain(program.stmts.iter()) {
            match stmt {
                Stmt::Type(td) => {
                    self.declared_types.insert(td.name.clone());
                }
                Stmt::TypeAlias {
                    name, params, ty, ..
                } => {
                    self.declared_types.insert(name.clone());
                    self.type_aliases
                        .insert(name.clone(), (params.clone(), ty.clone()));
                }
                _ => {}
            }
        }
        self.resolve_variant_payload_types();

        // Pre-pass 2: operator-to-trait registry. Fail-fast.
        for stmt in seed_stmts.iter().chain(program.stmts.iter()) {
            if let Stmt::Trait(td) = stmt {
                if let Err(err) = validate_trait_methods_have_target(td) {
                    return (ModuleInference::default(), vec![err]);
                }
                self.trait_env.insert(td.name.clone(), td.clone());
                for method in &td.methods {
                    if method.fixity.is_some() {
                        match self.op_trait_map.get(&method.name) {
                            Some(existing) if existing != &td.name => {
                                return (
                                    ModuleInference::default(),
                                    vec![
                                        TypeError::DuplicateOperator(method.name.clone())
                                            .at(stmt.span()),
                                    ],
                                );
                            }
                            Some(_) => {}
                            None => {
                                self.op_trait_map
                                    .insert(method.name.clone(), td.name.clone());
                            }
                        }
                    }
                }
            }
        }
        // Seed this program's own impl dictionaries for standalone inference. Graph
        // inference also calls set_known_impl_dicts with the full module env; the
        // overlap is harmless and keeps both entry points on the same call path.
        self.register_impl_dict_names(seed_stmts.iter().chain(program.stmts.iter()));

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
                    let mut param_vars = HashMap::new();
                    match self.ast_to_ty_with_vars(ty, &mut param_vars) {
                        Ok(t) => {
                            let scheme = self.generalize(&env, t);
                            self.definition_schemes.insert(*name_span, scheme.clone());
                            env.insert(
                                name.clone(),
                                EnvInfo {
                                    scheme,
                                    is_mutable: false,
                                },
                            );
                        }
                        Err(err) => {
                            unavailable.extend(bound);
                            diagnostics.push(err.at(span));
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

            let snapshot = InferSnapshot {
                subst_map: self.subst.snapshot_map(),
                pending_constraints: self.pending_constraints.clone(),
                loop_break_tys: self.loop_break_tys.clone(),
                fn_return_tys: self.fn_return_tys.clone(),
                expr_types: self.expr_types.clone(),
                symbol_types: self.symbol_types.clone(),
                binding_types: self.binding_types.clone(),
                definition_schemes: self.definition_schemes.clone(),
                env: env.clone(),
            };

            match self.infer_stmt(&mut env, stmt) {
                Ok(stmt_ty) => {
                    value_ty = if matches!(stmt, Stmt::Expr(_)) {
                        stmt_ty
                    } else {
                        Ty::Unit
                    };
                    // A successful redefinition shadows any prior failure of the same name.
                    unavailable.remove_all(&bound);
                    succeeded[idx] = true;
                }
                Err(err) => {
                    self.subst.restore_map(snapshot.subst_map);
                    self.pending_constraints = snapshot.pending_constraints;
                    self.loop_break_tys = snapshot.loop_break_tys;
                    self.fn_return_tys = snapshot.fn_return_tys;
                    self.expr_types = snapshot.expr_types;
                    self.symbol_types = snapshot.symbol_types;
                    self.binding_types = snapshot.binding_types;
                    self.definition_schemes = snapshot.definition_schemes;
                    env = snapshot.env;
                    unavailable.extend(bound);
                    diagnostics.push(err);
                }
            }
        }

        for info in env.0.values_mut() {
            info.scheme.ty = self.subst.apply(&info.scheme.ty);
        }

        // Final pass on succeeded statements only — restored statements may carry pending
        // dictionary args that reference type variables from the discarded inference.
        for (stmt, &ok) in program.stmts.iter_mut().zip(succeeded.iter()) {
            if !ok {
                continue;
            }
            let span = stmt.span();
            let resolver = |p: &PendingDictArg| resolve_concrete(p, &self.subst);
            if let Err(err) = final_pass_stmt(stmt, &resolver) {
                diagnostics.push(err.at(span));
            }
        }

        let expr_types = self
            .expr_types
            .iter()
            .map(|(id, ty)| (*id, self.subst.apply(ty)))
            .collect();
        let symbol_types = self
            .symbol_types
            .iter()
            .map(|(id, ty)| (*id, self.subst.apply(ty)))
            .collect();
        let binding_types = self
            .binding_types
            .iter()
            .map(|(span, ty)| (*span, self.subst.apply(ty)))
            .collect();
        let definition_schemes = self
            .definition_schemes
            .iter()
            .map(|(span, scheme)| (*span, self.subst.apply_scheme(scheme)))
            .collect();

        (
            ModuleInference {
                env,
                variant_env: self.variant_env.clone(),
                value_ty: self.subst.apply(&value_ty),
                expr_types,
                symbol_types,
                binding_types,
                definition_schemes,
            },
            diagnostics,
        )
    }

    fn reset_program_state(&mut self) {
        self.type_aliases.clear();
        self.declared_types.clear();
        self.declared_types
            .extend(["string", "bool", "Array", "Iter"].map(str::to_string));
        self.pending_constraints.clear();
        self.loop_break_tys.clear();
        self.fn_return_tys.clear();
        self.expr_types.clear();
        self.symbol_types.clear();
        self.binding_types.clear();
        self.definition_schemes.clear();
    }

    fn register_impl_dict_names<'a>(&mut self, stmts: impl Iterator<Item = &'a Stmt>) {
        for stmt in stmts {
            if let Stmt::Impl(impl_def) = stmt {
                self.known_impl_dicts.insert(format!(
                    "__{}__{}",
                    impl_def.trait_name,
                    impl_target_name(&impl_def.target)
                ));
            }
        }
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
                let value_ty = self.infer_expr(env, value)?;

                let inferred_ty = if let Some(ast_ty) = ty {
                    let mut param_vars = HashMap::new();
                    let expected_ty = self.ast_to_ty_with_vars(ast_ty, &mut param_vars)?;
                    unify(&mut self.subst, expected_ty.clone(), value_ty)
                        .map_err(|err| err.at(value.span))?;
                    expected_ty
                } else {
                    value_ty
                };

                // Reject refutable patterns in let position.
                if !is_irrefutable_let(pat) {
                    return Err(TypeError::RefutableLetPattern.at(value.span));
                }

                // For a simple variable binding, support let-polymorphism.
                if let Pattern::Variable(name, span) = pat {
                    self.binding_types.insert(*span, inferred_ty.clone());
                    let scheme = if *is_mutable || !is_value(&*value) {
                        Scheme::mono(inferred_ty)
                    } else {
                        self.generalize(env, inferred_ty)
                    };
                    env.insert(
                        name.clone(),
                        EnvInfo {
                            scheme,
                            is_mutable: *is_mutable,
                        },
                    );
                } else {
                    // Destructuring: bind each pattern variable, then generalize if
                    // the RHS is a syntactic value (preserving let-polymorphism).
                    //
                    // Snapshot env free vars BEFORE inserting new bindings so that
                    // sibling bindings don't prevent each other from being generalized.
                    let pre_let_env_vars: HashSet<TyVar> = if !*is_mutable && is_value(&*value) {
                        env.free_vars(&self.subst)
                    } else {
                        HashSet::new()
                    };
                    self.check_pattern(pat, inferred_ty, env, *is_mutable)?;
                    if !*is_mutable && is_value(&*value) {
                        let mut bound = std::collections::HashSet::new();
                        insert_pattern_bindings(&mut bound, pat);
                        let updates: Vec<(String, Ty, bool)> = bound
                            .iter()
                            .filter_map(|name| {
                                env.get(name).map(|info| {
                                    (name.clone(), info.scheme.ty.clone(), info.is_mutable)
                                })
                            })
                            .collect();
                        for (name, ty, is_mut) in updates {
                            let applied = self.subst.apply(&ty);
                            let ty_vars = free_type_vars(&applied);
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
                                EnvInfo {
                                    scheme,
                                    is_mutable: is_mut,
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
            Stmt::Expr(expr) => self.infer_expr(env, expr),
        })();
        result.map_err(|err| err.with_span_if_absent(span))
    }

    fn add_constructors_to_env(
        &mut self,
        env: &mut TypeEnv,
        td: &TypeDef,
    ) -> Result<(), TypeError> {
        let mut param_map: HashMap<String, TyVar> = HashMap::new();
        let mut quantified: Vec<TyVar> = Vec::new();
        let mut type_args: Vec<Ty> = Vec::new();

        for p in &td.params {
            let v = self.fresh_var();
            param_map.insert(p.clone(), v);
            quantified.push(v);
            type_args.push(Ty::Var(v));
        }

        let result_ty = if type_args.is_empty() {
            Ty::Con(td.name.clone())
        } else {
            Ty::App(Box::new(Ty::Con(td.name.clone())), type_args)
        };

        let mut entries = Vec::new();
        for variant in &td.variants {
            let ty = match &variant.payload {
                None => result_ty.clone(),
                Some(payload_ast) => {
                    let mut pm = param_map.clone();
                    let payload_ty = self.ast_to_ty_with_vars(payload_ast, &mut pm)?;
                    Ty::Func(vec![payload_ty], Box::new(result_ty.clone()))
                }
            };
            entries.push((
                variant.name.clone(),
                EnvInfo {
                    scheme: Scheme {
                        vars: quantified.clone(),
                        constraints: vec![],
                        ty,
                    },
                    is_mutable: false,
                },
            ));
        }
        for (name, info) in entries {
            env.insert(name, info);
        }
        for variant in &td.variants {
            if let Some(info) = env.get(&variant.name) {
                self.definition_schemes
                    .insert(variant.name_span, info.scheme.clone());
            }
        }
        Ok(())
    }

    fn resolve_variant_payload_types(&mut self) {
        let variants: Vec<(String, Vec<String>, Option<Type>)> = self
            .variant_env
            .0
            .iter()
            .map(|(name, info)| (name.clone(), info.type_params.clone(), info.payload.clone()))
            .collect();

        for (name, type_params, payload) in variants {
            let mut param_vars = HashMap::new();
            let type_param_vars: Vec<TyVar> = type_params
                .iter()
                .map(|param| {
                    let var = self.fresh_var();
                    param_vars.insert(param.clone(), var);
                    var
                })
                .collect();

            let payload_ty = payload
                .as_ref()
                .and_then(|ty| self.ast_to_ty_with_vars(ty, &mut param_vars).ok());

            if let Some(info) = self.variant_env.0.get_mut(&name) {
                info.type_param_vars = type_param_vars;
                info.payload_ty = payload_ty;
            }
        }
    }

    fn discard_failed_type_decl(&mut self, td: &TypeDef) {
        self.declared_types.remove(&td.name);
        for variant in &td.variants {
            self.variant_env.0.remove(&variant.name);
        }
    }

    fn infer_impl(&mut self, env: &mut TypeEnv, id: &mut ImplDef) -> Result<(), SpannedTypeError> {
        let trait_def = self
            .trait_env
            .get(&id.trait_name)
            .ok_or_else(|| TypeError::UnknownTrait(id.trait_name.clone()))?
            .clone();

        let impl_target = impl_target_name(&id.target);

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

            let mut param_vars: HashMap<String, TyVar> = HashMap::new();
            let mut param_tys: Vec<Ty> = Vec::new();
            let mut body_env = env.clone();

            for ((p_pat, p_type_opt), derived_ty) in
                impl_method.params.iter().zip(derived_params.iter())
            {
                if !is_irrefutable_param(p_pat) {
                    return Err(TypeError::RefutableParamPattern.at(impl_method.body.span));
                }
                let p_ty = self.ast_to_ty_with_vars(derived_ty, &mut param_vars)?;
                if let Some(p_type) = p_type_opt {
                    let explicit_ty = self.ast_to_ty_with_vars(p_type, &mut param_vars)?;
                    unify(&mut self.subst, p_ty.clone(), explicit_ty)
                        .map_err(|err| err.at(impl_method.body.span))?;
                }
                param_tys.push(p_ty.clone());
                self.check_pattern(p_pat, p_ty, &mut body_env, false)?;
            }
            let ret_ty = self.ast_to_ty_with_vars(&derived_ret, &mut param_vars)?;

            if let Some(ret_type_opt) = &impl_method.ret_type {
                let explicit_ret = self.ast_to_ty_with_vars(ret_type_opt, &mut param_vars)?;
                unify(&mut self.subst, ret_ty.clone(), explicit_ret)
                    .map_err(|err| err.at(impl_method.body.span))?;
            }

            self.fn_return_tys.push(ret_ty.clone());
            let body_ty = self.infer_expr(&body_env, &mut impl_method.body)?;
            self.fn_return_tys.pop();
            unify(&mut self.subst, body_ty, ret_ty.clone())
                .map_err(|err| err.at(impl_method.body.span))?;

            let method_ty = Ty::Func(param_tys, Box::new(ret_ty));
            self.definition_schemes
                .insert(impl_method.name_span, Scheme::mono(method_ty.clone()));
            dict_fields.push((impl_method.name.clone(), method_ty));
        }

        dict_fields.sort_by(|(a, _), (b, _)| a.cmp(b));
        let dict_ty = Ty::Record(Row {
            fields: dict_fields,
            tail: Box::new(Ty::Unit),
        });
        let dict_scheme = self.generalize(env, dict_ty);
        let dict_name = format!("__{}__{}", id.trait_name, impl_target);
        env.insert(
            dict_name,
            EnvInfo {
                scheme: dict_scheme,
                is_mutable: false,
            },
        );
        Ok(())
    }

    fn infer_expr(&mut self, env: &TypeEnv, expr: &mut Expr) -> Result<Ty, SpannedTypeError> {
        let result: Result<Ty, SpannedTypeError> = match &mut expr.kind {
            ExprKind::Number(_) => Ok(Ty::F64),
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
                    let ty = self.instantiate_value(&info.scheme);
                    if expr.id != 0 {
                        self.symbol_types.insert(expr.id, self.subst.apply(&ty));
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
                        if !info.is_mutable {
                            return Err(TypeError::ImmutableAssignment(name.clone()).into());
                        }
                        let ty = self.instantiate(&info.scheme);
                        if target.id != 0 {
                            self.symbol_types.insert(target.id, self.subst.apply(&ty));
                        }
                        ty
                    }
                    ExprKind::FieldAccess { .. } => {
                        if let Some(name) = find_assignment_base_name(target) {
                            let info = env
                                .get(&name)
                                .ok_or_else(|| TypeError::UnboundVariable(name.clone()))?;
                            if !info.is_mutable {
                                return Err(TypeError::ImmutableAssignment(name.clone()).into());
                            }
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
            } => {
                let l_ty = self.infer_expr(env, lhs)?;
                let r_ty = self.infer_expr(env, rhs)?;
                match op {
                    BinOp::Pipe => {
                        // Fast path: if RHS is a constrained identifier, resolve its dict args.
                        if let ExprKind::Ident(callee_name) = &rhs.kind
                            && let Some(info) = env.get(callee_name.as_str())
                        {
                            let scheme = info.scheme.clone();
                            if !scheme.constraints.is_empty() {
                                return self.infer_constrained_apply(
                                    &scheme,
                                    vec![l_ty],
                                    dict_args,
                                    pending_dict_args,
                                );
                            }
                        }
                        let ret_var = self.fresh_var();
                        let expected_r_ty = Ty::Func(vec![l_ty], Box::new(Ty::Var(ret_var)));
                        unify(&mut self.subst, r_ty, expected_r_ty)?;
                        Ok(self.subst.apply(&Ty::Var(ret_var)))
                    }
                    BinOp::Custom(op) => {
                        if let Some(trait_name) = self.op_trait_map.get(op.as_str()).cloned() {
                            let trait_def = self
                                .trait_env
                                .get(&trait_name)
                                .ok_or_else(|| TypeError::UnknownTrait(trait_name.clone()))?
                                .clone();
                            let method = trait_def
                                .methods
                                .iter()
                                .find(|m| m.name == *op)
                                .ok_or_else(|| TypeError::UnknownTraitMethod {
                                    trait_name: trait_name.clone(),
                                    method: op.clone(),
                                })?
                                .clone();

                            let mut param_vars: HashMap<String, TyVar> = HashMap::new();
                            let target_var = self.fresh_var();
                            param_vars.insert(trait_def.param.clone(), target_var);

                            let lhs_param_ty =
                                self.ast_to_ty_with_vars(&method.params[0].1, &mut param_vars)?;
                            let rhs_param_ty =
                                self.ast_to_ty_with_vars(&method.params[1].1, &mut param_vars)?;
                            let ret_ty =
                                self.ast_to_ty_with_vars(&method.ret_type, &mut param_vars)?;

                            unify(&mut self.subst, l_ty, lhs_param_ty)?;

                            let resolved_target = self.subst.apply(&Ty::Var(target_var));
                            match ty_target_name(&resolved_target) {
                                None => {
                                    if let Ty::Var(v) = resolved_target {
                                        self.pending_constraints.push(TraitConstraint {
                                            var: v,
                                            trait_name: trait_name.clone(),
                                        });
                                        *pending_op = Some(PendingDictArg {
                                            var: v,
                                            trait_name: trait_name.clone(),
                                        });
                                    }
                                }
                                Some(target_name) => {
                                    *resolved_op = Some(format!(
                                        "__{}__{}.{}",
                                        trait_name,
                                        target_name,
                                        mangle_op(op)
                                    ));
                                }
                            }

                            unify(&mut self.subst, r_ty, rhs_param_ty)?;
                            Ok(self.subst.apply(&ret_ty))
                        } else {
                            // op is a regular (non-trait) operator function
                            if let Some(info) = env.get(op.as_str()) {
                                let scheme = info.scheme.clone();
                                if !scheme.constraints.is_empty() {
                                    let ret_ty = self.infer_constrained_apply(
                                        &scheme,
                                        vec![l_ty, r_ty],
                                        dict_args,
                                        pending_dict_args,
                                    )?;
                                    *resolved_op = Some(mangle_op(op));
                                    return Ok(ret_ty);
                                }
                            }
                            let fn_ty = env
                                .get(op.as_str())
                                .map(|info| self.instantiate(&info.scheme))
                                .ok_or_else(|| TypeError::UnboundVariable(op.clone()))?;
                            let ret_var = self.fresh_var();
                            let expected = Ty::Func(vec![l_ty, r_ty], Box::new(Ty::Var(ret_var)));
                            unify(&mut self.subst, fn_ty, expected)?;
                            Ok(self.subst.apply(&Ty::Var(ret_var)))
                        }
                    }
                }
            }
            ExprKind::Call {
                callee,
                args,
                arg_wrappers,
                resolved_callee,
                dict_args,
                pending_dict_args,
            } => {
                // Trait method call: `TraitName.method(args...)`.
                if let ExprKind::FieldAccess { expr, field, .. } = &mut callee.kind
                    && let ExprKind::Ident(trait_name) = &expr.kind
                    && let Some(trait_def) = self.trait_env.get(trait_name).cloned()
                {
                    let method = trait_def
                        .methods
                        .iter()
                        .find(|m| m.name == *field)
                        .ok_or_else(|| TypeError::UnknownTraitMethod {
                            trait_name: trait_name.clone(),
                            method: field.clone(),
                        })?
                        .clone();

                    return self.resolve_trait_method_call(
                        env,
                        args,
                        arg_wrappers,
                        resolved_callee,
                        trait_def,
                        method,
                        "trait method call",
                    );
                }

                // Bare trait method call: `method(args...)` without explicit `Trait.` prefix.
                // This is call-only sugar: bare trait methods are not first-class values,
                // because dispatch is resolved from the first argument's concrete target.
                // Allowed only when the method name belongs to exactly one trait in scope.
                if let ExprKind::Ident(method_name) = &callee.kind
                    && env.get(method_name.as_str()).is_none()
                {
                    if let Some(resolved) = self.bare_trait_method(method_name)? {
                        return self.resolve_trait_method_call(
                            env,
                            args,
                            arg_wrappers,
                            resolved_callee,
                            resolved.trait_def,
                            resolved.method,
                            "bare trait method call",
                        );
                    }
                }

                // Constrained function call: resolve dict args
                if let ExprKind::Ident(callee_name) = &callee.kind
                    && let Some(info) = env.get(callee_name.as_str())
                {
                    let scheme = info.scheme.clone();
                    if !scheme.constraints.is_empty() {
                        // Record the instantiated callee type so hover/tooling can show its type.
                        // The normal plain-call path does this via infer_expr(callee), but the
                        // constrained path bypasses that and must record it explicitly.
                        if callee.id != 0 {
                            let instantiated = self.instantiate_value(&scheme);
                            self.symbol_types
                                .insert(callee.id, self.subst.apply(&instantiated));
                        }
                        let arg_tys = self.infer_args(env, args, arg_wrappers)?;
                        return self.infer_constrained_apply(
                            &scheme,
                            arg_tys,
                            dict_args,
                            pending_dict_args,
                        );
                    }
                }

                // Plain call
                let mut callee_ty = self.infer_expr(env, callee)?;
                callee_ty = self.subst.apply(&callee_ty);
                let callee_constraints = if let Ty::Qualified(constraints, inner) = callee_ty {
                    callee_ty = *inner;
                    constraints
                } else {
                    Vec::new()
                };
                let arg_tys = self.infer_args(env, args, arg_wrappers)?;
                let ret_ty = Ty::Var(self.fresh_var());
                unify(
                    &mut self.subst,
                    callee_ty,
                    Ty::Func(arg_tys, Box::new(ret_ty.clone())),
                )?;
                attach_dict_args(
                    dict_args,
                    pending_dict_args,
                    &mut self.pending_constraints,
                    &callee_constraints,
                    &self.subst,
                );
                Ok(self.subst.apply(&ret_ty))
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
                unify(&mut self.subst, then_ty.clone(), else_ty)?;
                Ok(then_ty)
            }
            ExprKind::Match { scrutinee, arms } => {
                let scrutinee_ty = self.infer_expr(env, scrutinee)?;
                let result_ty = self.subst.fresh_var();
                for (pattern, arm_expr) in &mut *arms {
                    let mut arm_env = env.clone();
                    let s_ty = self.subst.apply(&scrutinee_ty);
                    self.check_pattern(pattern, s_ty, &mut arm_env, false)?;
                    let arm_ty = self.infer_expr(&arm_env, arm_expr)?;
                    unify(&mut self.subst, result_ty.clone(), arm_ty)?;
                }
                let s_ty = self.subst.apply(&scrutinee_ty);
                self.check_exhaustive(arms, &s_ty)?;
                Ok(result_ty)
            }
            ExprKind::Loop(body) => {
                let break_ty = self.subst.fresh_var();
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
                    unify(&mut self.subst, break_ty, val_ty)?;
                } else {
                    unify(&mut self.subst, break_ty, Ty::Unit)?;
                }
                Ok(self.subst.fresh_var())
            }
            ExprKind::Continue => {
                if self.loop_break_tys.is_empty() {
                    Err(TypeError::ContinueOutsideLoop.into())
                } else {
                    Ok(self.subst.fresh_var())
                }
            }
            ExprKind::Return(val) => {
                let ret_ty = self
                    .fn_return_tys
                    .last()
                    .cloned()
                    .ok_or(TypeError::ReturnOutsideFunction)?;
                if let Some(val_expr) = val {
                    let val_ty = self.infer_expr(env, val_expr)?;
                    unify(&mut self.subst, ret_ty, val_ty)?;
                } else {
                    unify(&mut self.subst, ret_ty, Ty::Unit)?;
                }
                Ok(self.subst.fresh_var())
            }
            ExprKind::Block { stmts, final_expr } => {
                let mut block_env = env.clone();
                for stmt in stmts.iter_mut() {
                    self.infer_stmt(&mut block_env, stmt)?;
                    if stmt_always_exits(stmt, true) {
                        return Ok(self.subst.fresh_var());
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
            ExprKind::Array(entries) => {
                let elt_ty = self.subst.fresh_var();
                for entry in entries {
                    match entry {
                        ArrayEntry::Elem(expr) => {
                            let ty = self.infer_expr(env, expr)?;
                            unify(&mut self.subst, elt_ty.clone(), ty)?;
                        }
                        ArrayEntry::Spread(expr) => {
                            let ty = self.infer_expr(env, expr)?;
                            let expected = Ty::App(
                                Box::new(Ty::Con("Array".to_string())),
                                vec![elt_ty.clone()],
                            );
                            unify(&mut self.subst, ty, expected)?;
                        }
                    }
                }
                Ok(Ty::App(
                    Box::new(Ty::Con("Array".to_string())),
                    vec![elt_ty],
                ))
            }
            ExprKind::Record(entries) => {
                let mut field_tys: Vec<(String, Ty)> = Vec::new();
                let mut has_spread = false;
                for entry in entries {
                    match entry {
                        RecordEntry::Field(name, expr) => {
                            let ty = self.infer_expr(env, expr)?;
                            if let Some(pos) = field_tys.iter().position(|(n, _)| n == name) {
                                field_tys[pos].1 = ty;
                            } else {
                                field_tys.push((name.clone(), ty));
                            }
                        }
                        RecordEntry::Spread(expr) => {
                            has_spread = true;
                            let spread_ty = self.infer_expr(env, expr)?;
                            let tail_var = self.subst.fresh_var();
                            unify(
                                &mut self.subst,
                                spread_ty,
                                Ty::Record(Row {
                                    fields: vec![],
                                    tail: Box::new(tail_var),
                                }),
                            )?;
                        }
                    }
                }
                field_tys.sort_by(|(a, _), (b, _)| a.cmp(b));
                let tail = if has_spread {
                    self.subst.fresh_var()
                } else {
                    Ty::Unit
                };
                Ok(Ty::Record(Row {
                    fields: field_tys,
                    tail: Box::new(tail),
                }))
            }
            ExprKind::FieldAccess { expr, field, .. } => {
                let expr_ty = self.infer_expr(env, expr)?;
                let field_ty = self.subst.fresh_var();
                let tail = self.subst.fresh_var();
                let expected = Ty::Record(Row {
                    fields: vec![(field.clone(), field_ty.clone())],
                    tail: Box::new(tail),
                });
                unify(&mut self.subst, expr_ty, expected)?;
                Ok(field_ty)
            }
            ExprKind::Lambda {
                params,
                body,
                dict_params,
            } => {
                let mut param_vars: HashMap<String, TyVar> = HashMap::new();
                let mut param_tys = Vec::new();
                let mut body_env = env.clone();
                for (pat, p_type) in params.iter() {
                    if !is_irrefutable_param(pat) {
                        return Err(TypeError::RefutableParamPattern.at(body.span));
                    }
                    let p_ty = match p_type {
                        Some(t) => self.ast_to_ty_with_vars(t, &mut param_vars)?,
                        None => self.subst.fresh_var(),
                    };
                    param_tys.push(p_ty.clone());
                    self.check_pattern(pat, p_ty, &mut body_env, false)?;
                }

                let saved_pending = std::mem::take(&mut self.pending_constraints);

                let ret_var = self.fresh_var();
                let ret_ty = Ty::Var(ret_var);
                self.fn_return_tys.push(ret_ty.clone());
                let body_ty = self.infer_expr(&body_env, body)?;
                self.fn_return_tys.pop();
                unify(&mut self.subst, body_ty, ret_ty.clone())?;

                let fn_ty = Ty::Func(param_tys, Box::new(self.subst.apply(&ret_ty)));
                let fn_constraints =
                    std::mem::replace(&mut self.pending_constraints, saved_pending);
                let finalized = self.finalize_constraints(env, fn_ty, fn_constraints);
                self.pending_constraints.extend(finalized.bubbled.clone());
                *dict_params = finalized.owned.iter().map(dict_param_name).collect();

                let resolver = |p: &PendingDictArg| {
                    resolve_local_or_concrete(p, &finalized.owned, &self.subst)
                };
                if finalized.bubbled.is_empty() {
                    resolve_dict_uses_expr(body, &resolver, false)?;
                } else {
                    // Bubbled constraints belong to an enclosing callable. They
                    // are deliberately absent from this lambda's owned dict
                    // params, so this pass must leave those pending uses for the
                    // enclosing resolver instead of reporting them as unresolved.
                    resolve_dict_uses_expr_lenient(body, &resolver, false)?;
                }

                Ok(if finalized.owned.is_empty() {
                    finalized.scheme.ty
                } else {
                    Ty::Qualified(finalized.owned, Box::new(finalized.scheme.ty))
                })
            }
            ExprKind::For {
                pat,
                iterable,
                body,
                resolved_iter,
                pending_iter,
            } => {
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
                param_vars.insert(iterable_trait.param.clone(), target_var);

                let self_ty =
                    self.ast_to_ty_with_vars(&iter_method.params[0].1, &mut param_vars)?;
                let ret_ty = self.ast_to_ty_with_vars(&iter_method.ret_type, &mut param_vars)?;

                unify(&mut self.subst, iter_ty, self_ty)?;

                let resolved_target = self.subst.apply(&Ty::Var(target_var));
                match ty_target_name(&resolved_target) {
                    None => {
                        if let Ty::Var(v) = resolved_target {
                            self.pending_constraints.push(TraitConstraint {
                                var: v,
                                trait_name: "Iterable".to_string(),
                            });
                            *pending_iter = Some(PendingDictArg {
                                var: v,
                                trait_name: "Iterable".to_string(),
                            });
                        } else {
                            return Err(TypeError::UnresolvedTrait {
                                context: "for loop".to_string(),
                                trait_name: "Iterable".to_string(),
                            }
                            .into());
                        }
                    }
                    Some(target_name) => {
                        *resolved_iter = Some(format!("__Iterable__{}.iter", target_name));
                    }
                }

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
        };
        if let Ok(ty) = &result
            && expr.id != 0
        {
            self.expr_types.insert(expr.id, self.subst.apply(ty));
        }
        result.map_err(|err: SpannedTypeError| err.with_span_if_absent(expr.span))
    }

    fn resolve_trait_method_call(
        &mut self,
        env: &TypeEnv,
        args: &mut [Expr],
        arg_wrappers: &mut Vec<Option<ArgWrapper>>,
        resolved_callee: &mut Option<String>,
        trait_def: TraitDef,
        method: TraitMethod,
        context: &str,
    ) -> Result<Ty, SpannedTypeError> {
        let trait_name = trait_def.name.clone();
        let method_name = method.name.clone();
        let arg_tys = self.infer_args(env, args, arg_wrappers)?;

        let Some(first_arg_ty) = arg_tys.first() else {
            return Err(TypeError::ArityMismatch {
                expected: method.params.len(),
                got: 0,
            }
            .into());
        };
        if arg_tys.len() != method.params.len() {
            return Err(TypeError::ArityMismatch {
                expected: method.params.len(),
                got: arg_tys.len(),
            }
            .into());
        }
        let resolved_target = self.subst.apply(first_arg_ty);
        let target_name =
            ty_target_name(&resolved_target).ok_or_else(|| TypeError::UnresolvedTrait {
                context: context.to_string(),
                trait_name: trait_name.clone(),
            })?;
        let dict_name = format!("__{}__{}", trait_name, target_name);

        let ret_ty =
            if let Some(dict_info) = env.get(&dict_name) {
                let dict_ty = self.instantiate(&dict_info.scheme);
                let method_ty = record_field_ty(&self.subst.apply(&dict_ty), &method_name)
                    .ok_or_else(|| TypeError::UnknownTraitMethod {
                        trait_name: trait_name.clone(),
                        method: method_name.clone(),
                    })?;
                let ret_ty = Ty::Var(self.fresh_var());
                unify(
                    &mut self.subst,
                    method_ty,
                    Ty::Func(arg_tys, Box::new(ret_ty.clone())),
                )?;
                ret_ty
            } else if self.known_impl_dicts.contains(&dict_name) {
                self.check_trait_method_signature(&trait_def, &method, arg_tys, context)?
            } else {
                return Err(TypeError::MissingTraitImpl {
                    trait_name: trait_name.clone(),
                    impl_target: target_name.to_string(),
                }
                .into());
            };

        *resolved_callee = Some(format!(
            "__{}__{}.{}",
            trait_name,
            target_name,
            mangle_op(&method_name)
        ));
        Ok(self.subst.apply(&ret_ty))
    }

    fn check_trait_method_signature(
        &mut self,
        trait_def: &TraitDef,
        method: &TraitMethod,
        arg_tys: Vec<Ty>,
        context: &str,
    ) -> Result<Ty, SpannedTypeError> {
        let mut param_vars = HashMap::new();
        let target_var = self.fresh_var();
        param_vars.insert(trait_def.param.clone(), target_var);
        let method_param_tys: Vec<Ty> = method
            .params
            .iter()
            .map(|(_, p_ty)| self.ast_to_ty_with_vars(p_ty, &mut param_vars))
            .collect::<Result<_, _>>()?;
        let ret_ty = self.ast_to_ty_with_vars(&method.ret_type, &mut param_vars)?;
        for (arg_ty, expected_ty) in arg_tys.into_iter().zip(method_param_tys) {
            unify(&mut self.subst, expected_ty, arg_ty)?;
        }
        let resolved_target = self.subst.apply(&Ty::Var(target_var));
        ty_target_name(&resolved_target).ok_or_else(|| TypeError::UnresolvedTrait {
            context: context.to_string(),
            trait_name: trait_def.name.clone(),
        })?;
        Ok(ret_ty)
    }

    fn bare_trait_method(
        &self,
        method_name: &str,
    ) -> Result<Option<ResolvedTraitMethod>, TypeError> {
        let mut matching: Vec<_> = self
            .trait_env
            .values()
            .filter_map(|trait_def| {
                trait_def
                    .methods
                    .iter()
                    .find(|method| method.name == method_name)
                    .map(|method| ResolvedTraitMethod {
                        trait_def: trait_def.clone(),
                        method: method.clone(),
                    })
            })
            .collect();
        matching.sort_by(|a, b| a.trait_def.name.cmp(&b.trait_def.name));

        if matching.len() > 1 {
            return Err(TypeError::AmbiguousTraitMethod {
                method: method_name.to_string(),
                candidates: matching
                    .iter()
                    .map(|candidate| candidate.trait_def.name.clone())
                    .collect(),
            });
        }

        Ok(matching.into_iter().next())
    }

    fn infer_args(
        &mut self,
        env: &TypeEnv,
        args: &mut [Expr],
        arg_wrappers: &mut Vec<Option<ArgWrapper>>,
    ) -> Result<Vec<Ty>, SpannedTypeError> {
        arg_wrappers.clear();
        let mut arg_tys = Vec::with_capacity(args.len());
        for arg in args {
            let inferred = self.infer_expr(env, arg)?;
            let mut arg_ty = self.subst.apply(&inferred);
            let wrapper = if let Ty::Qualified(constraints, inner) = arg_ty {
                let mut wrapper = ArgWrapper {
                    dict_args: Vec::new(),
                    pending_dict_args: Vec::new(),
                };
                attach_dict_args(
                    &mut wrapper.dict_args,
                    &mut wrapper.pending_dict_args,
                    &mut self.pending_constraints,
                    &constraints,
                    &self.subst,
                );
                arg_ty = *inner;
                Some(wrapper)
            } else {
                None
            };
            arg_wrappers.push(wrapper);
            arg_tys.push(arg_ty);
        }
        Ok(arg_tys)
    }

    fn infer_constrained_apply(
        &mut self,
        scheme: &Scheme,
        arg_tys: Vec<Ty>,
        dict_args: &mut Vec<String>,
        pending_dict_args: &mut Vec<PendingDictArg>,
    ) -> Result<Ty, SpannedTypeError> {
        let instantiated = self.instantiate_scheme(scheme);
        let ret_ty = Ty::Var(self.fresh_var());
        unify(
            &mut self.subst,
            instantiated.ty,
            Ty::Func(arg_tys, Box::new(ret_ty.clone())),
        )?;
        attach_dict_args(
            dict_args,
            pending_dict_args,
            &mut self.pending_constraints,
            &instantiated.constraints,
            &self.subst,
        );
        Ok(self.subst.apply(&ret_ty))
    }

    fn check_pattern(
        &mut self,
        pat: &Pattern,
        scrutinee_ty: Ty,
        env: &mut TypeEnv,
        is_mutable: bool,
    ) -> Result<(), TypeError> {
        match pat {
            Pattern::Wildcard => Ok(()),
            Pattern::StringLit(_) => {
                unify(&mut self.subst, scrutinee_ty, Ty::Con("string".to_string()))
            }
            Pattern::Variable(name, span) => {
                self.binding_types.insert(*span, scrutinee_ty.clone());
                env.insert(
                    name.clone(),
                    EnvInfo {
                        scheme: Scheme::mono(scrutinee_ty),
                        is_mutable,
                    },
                );
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

                if let Some((var_name, var_span)) = binding {
                    let payload_ty = match &info.payload {
                        Some(ast_ty) => self.ast_to_ty_with_vars(ast_ty, &mut param_map)?,
                        None => {
                            return Err(TypeError::UnboundVariable(format!(
                                "variant `{}` has no payload to bind",
                                name
                            )));
                        }
                    };
                    self.binding_types.insert(*var_span, payload_ty.clone());
                    env.insert(
                        var_name.clone(),
                        EnvInfo {
                            scheme: Scheme::mono(payload_ty),
                            is_mutable,
                        },
                    );
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
                    .map(|(field_name, _, _)| (field_name.clone(), self.subst.fresh_var()))
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
                        self.binding_types
                            .insert(*binding_span, self.subst.apply(field_ty));
                        env.insert(
                            binding_name.clone(),
                            EnvInfo {
                                scheme: Scheme::mono(self.subst.apply(field_ty)),
                                is_mutable,
                            },
                        );
                    }
                }

                if let Some(Some((rest_name, rest_span))) = rest {
                    let rest_ty = self.subst.apply(&Ty::Var(tail_var));
                    self.binding_types.insert(*rest_span, rest_ty.clone());
                    env.insert(
                        rest_name.clone(),
                        EnvInfo {
                            scheme: Scheme::mono(rest_ty),
                            is_mutable,
                        },
                    );
                }
                Ok(())
            }
            Pattern::List { elements, rest } => {
                let elt_ty = self.subst.fresh_var();
                let arr_ty = Ty::App(Box::new(Ty::Con("Array".to_string())), vec![elt_ty.clone()]);
                unify(&mut self.subst, scrutinee_ty, arr_ty.clone())?;

                for elem in elements {
                    self.check_pattern(elem, elt_ty.clone(), env, is_mutable)?;
                }
                if let Some(Some((rest_name, rest_span))) = rest {
                    self.binding_types.insert(*rest_span, arr_ty.clone());
                    env.insert(
                        rest_name.clone(),
                        EnvInfo {
                            scheme: Scheme::mono(arr_ty),
                            is_mutable,
                        },
                    );
                }
                Ok(())
            }
            Pattern::Tuple(pats) => {
                let elem_tys: Vec<Ty> = pats.iter().map(|_| self.subst.fresh_var()).collect();
                unify(&mut self.subst, scrutinee_ty, Ty::Tuple(elem_tys.clone()))?;
                for (p, t) in pats.iter().zip(elem_tys.iter()) {
                    let resolved = self.subst.apply(t);
                    self.check_pattern(p, resolved, env, is_mutable)?;
                }
                Ok(())
            }
        }
    }

    fn check_exhaustive(
        &self,
        arms: &[(Pattern, Expr)],
        scrutinee_ty: &Ty,
    ) -> Result<(), TypeError> {
        let patterns: Vec<&Pattern> = arms.iter().map(|(p, _)| p).collect();

        if patterns.iter().any(|p| pattern_is_catch_all(p)) {
            return Ok(());
        }

        match scrutinee_ty {
            Ty::Con(_) | Ty::App(_, _) => {
                let type_name = match scrutinee_ty {
                    Ty::Con(n) => n.clone(),
                    Ty::App(con, _) => match con.as_ref() {
                        Ty::Con(n) => n.clone(),
                        _ => {
                            return Err(TypeError::NonExhaustiveMatch {
                                missing: "non-exhaustive match — add a wildcard (_) arm"
                                    .to_string(),
                            });
                        }
                    },
                    _ => unreachable!(),
                };

                if type_name == "Array" {
                    return self.check_array_exhaustive(&patterns);
                }

                let type_variants: Vec<String> = self
                    .variant_env
                    .0
                    .iter()
                    .filter(|(_, vi)| vi.type_name == type_name)
                    .map(|(vname, _)| vname.clone())
                    .collect();

                if type_variants.is_empty() {
                    return Err(TypeError::NonExhaustiveMatch {
                        missing: "non-exhaustive match — add a wildcard (_) arm".to_string(),
                    });
                }

                let covered: HashSet<String> = patterns
                    .iter()
                    .filter_map(|p| {
                        if let Pattern::Constructor { name, .. } = p {
                            Some(name.clone())
                        } else {
                            None
                        }
                    })
                    .collect();

                let mut missing: Vec<_> = type_variants
                    .iter()
                    .filter(|v| !covered.contains(*v))
                    .collect();
                missing.sort();

                if missing.is_empty() {
                    Ok(())
                } else {
                    Err(TypeError::NonExhaustiveMatch {
                        missing: format!(
                            "missing constructors: {}",
                            missing
                                .iter()
                                .map(|s| s.as_str())
                                .collect::<Vec<_>>()
                                .join(", ")
                        ),
                    })
                }
            }
            _ => Err(TypeError::NonExhaustiveMatch {
                missing: "non-exhaustive match — add a wildcard (_) arm".to_string(),
            }),
        }
    }

    fn check_array_exhaustive(&self, patterns: &[&Pattern]) -> Result<(), TypeError> {
        let open_lens: Vec<usize> = patterns
            .iter()
            .filter_map(|p| {
                if let Pattern::List {
                    elements,
                    rest: Some(_),
                } = p
                {
                    Some(elements.len())
                } else {
                    None
                }
            })
            .collect();

        let exact_lens: HashSet<usize> = patterns
            .iter()
            .filter_map(|p| {
                if let Pattern::List {
                    elements,
                    rest: None,
                } = p
                {
                    Some(elements.len())
                } else {
                    None
                }
            })
            .collect();

        if open_lens.is_empty() {
            return Err(TypeError::NonExhaustiveMatch {
                missing: "non-exhaustive: arrays longer than the matched lengths are not covered \
                     — add [head, ..] or _ arm"
                    .to_string(),
            });
        }

        // open_lens.is_empty() returns early above, so min() always finds an element.
        let min_open = *open_lens.iter().min().unwrap();
        for len in 0..min_open {
            if !exact_lens.contains(&len) {
                let pat = if len == 0 {
                    "[]".to_string()
                } else {
                    format!("[{}]", (0..len).map(|_| "_").collect::<Vec<_>>().join(", "))
                };
                return Err(TypeError::NonExhaustiveMatch {
                    missing: format!("missing arm for arrays of length {} — add {}", len, pat),
                });
            }
        }

        Ok(())
    }

    fn ast_to_ty_with_vars(
        &mut self,
        ast_ty: &Type,
        param_vars: &mut HashMap<String, TyVar>,
    ) -> Result<Ty, TypeError> {
        Ok(match ast_ty {
            Type::Ident(name) => {
                if let Some((params, aliased_ty)) = self.type_aliases.get(name).cloned()
                    && params.is_empty()
                {
                    return self.ast_to_ty_with_vars(&aliased_ty, param_vars);
                }
                match name.as_str() {
                    "f64" => Ty::F64,
                    "Unit" | "()" => Ty::Unit,
                    _ if self.declared_types.contains(name) => Ty::Con(name.clone()),
                    _ => return Err(TypeError::UnknownType(name.clone())),
                }
            }
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
                    .map(|p| self.ast_to_ty_with_vars(p, param_vars))
                    .collect::<Result<_, _>>()?;
                Ty::Func(
                    param_tys,
                    Box::new(self.ast_to_ty_with_vars(ret, param_vars)?),
                )
            }
            Type::App(con, args) => {
                if let Type::Ident(name) = &**con
                    && let Some((params, aliased_ty)) = self.type_aliases.get(name).cloned()
                    && params.len() == args.len()
                {
                    let mut substituted = aliased_ty;
                    for (param, arg) in params.iter().zip(args.iter()) {
                        substituted = subst_hkt_param(&substituted, param, arg);
                    }
                    return self.ast_to_ty_with_vars(&substituted, param_vars);
                }
                let con_ty = self.ast_to_ty_with_vars(con, param_vars)?;
                let arg_tys = args
                    .iter()
                    .map(|a| self.ast_to_ty_with_vars(a, param_vars))
                    .collect::<Result<_, _>>()?;
                Ty::App(Box::new(con_ty), arg_tys)
            }
            Type::Tuple(tys) => Ty::Tuple(
                tys.iter()
                    .map(|t| self.ast_to_ty_with_vars(t, param_vars))
                    .collect::<Result<_, _>>()?,
            ),
            Type::Record(fields, is_open) => {
                let mut field_tys: Vec<_> = fields
                    .iter()
                    .map(|(n, t)| {
                        self.ast_to_ty_with_vars(t, param_vars)
                            .map(|ty| (n.clone(), ty))
                    })
                    .collect::<Result<_, _>>()?;
                field_tys.sort_by(|(a, _), (b, _)| a.cmp(b));
                let tail = if *is_open {
                    self.subst.fresh_var()
                } else {
                    Ty::Unit
                };
                Ty::Record(Row {
                    fields: field_tys,
                    tail: Box::new(tail),
                })
            }
            Type::Unit => Ty::Unit,
            Type::Hole => self.subst.fresh_var(),
        })
    }
}

// ── HKT substitution helpers ──────────────────────────────────────────────────

fn subst_hkt_param(ty: &Type, param: &str, target: &Type) -> Type {
    match ty {
        Type::App(con, args) if matches!(con.as_ref(), Type::Var(v) if v == param) => {
            if args.len() == 1 {
                apply_hole(target, &subst_hkt_param(&args[0], param, target))
            } else {
                ty.clone()
            }
        }
        Type::Var(v) if v == param => target.clone(),
        Type::App(con, args) => Type::App(
            Box::new(subst_hkt_param(con, param, target)),
            args.iter()
                .map(|a| subst_hkt_param(a, param, target))
                .collect(),
        ),
        Type::Func(params, ret) => Type::Func(
            params
                .iter()
                .map(|p| subst_hkt_param(p, param, target))
                .collect(),
            Box::new(subst_hkt_param(ret, param, target)),
        ),
        Type::Tuple(tys) => Type::Tuple(
            tys.iter()
                .map(|t| subst_hkt_param(t, param, target))
                .collect(),
        ),
        Type::Record(fields, open) => Type::Record(
            fields
                .iter()
                .map(|(n, t)| (n.clone(), subst_hkt_param(t, param, target)))
                .collect(),
            *open,
        ),
        other => other.clone(),
    }
}

fn apply_hole(target: &Type, arg: &Type) -> Type {
    if type_has_hole(target) {
        substitute_hole(target, arg)
    } else {
        Type::App(Box::new(target.clone()), vec![arg.clone()])
    }
}

fn type_has_hole(ty: &Type) -> bool {
    match ty {
        Type::Hole => true,
        Type::App(con, args) => type_has_hole(con) || args.iter().any(type_has_hole),
        _ => false,
    }
}

fn substitute_hole(ty: &Type, arg: &Type) -> Type {
    match ty {
        Type::Hole => arg.clone(),
        Type::App(con, args) => Type::App(
            Box::new(substitute_hole(con, arg)),
            args.iter().map(|a| substitute_hole(a, arg)).collect(),
        ),
        other => other.clone(),
    }
}

fn impl_target_name(target: &Type) -> String {
    match target {
        Type::Ident(name) => name.clone(),
        Type::App(con, _) => impl_target_name(con),
        _ => "Unknown".to_string(),
    }
}

fn validate_trait_methods_have_target(td: &TraitDef) -> Result<(), SpannedTypeError> {
    for method in &td.methods {
        if method.params.is_empty() {
            return Err(TypeError::TraitMethodMissingTarget {
                trait_name: td.name.clone(),
                method: method.name.clone(),
            }
            .at(method.span));
        }
    }
    Ok(())
}

/// Returns `true` if `pat` is irrefutable, i.e. always matches regardless of
/// the runtime value.  Only irrefutable patterns may appear in function-parameter
/// position; refutable patterns must use a `match` expression in the body.
fn is_irrefutable_param(pat: &Pattern) -> bool {
    match pat {
        Pattern::Variable(..) | Pattern::Wildcard => true,
        // Only OPEN records (with a rest binding) are irrefutable for fn params.
        // A closed record like #{ x } is refutable at runtime.
        Pattern::Record { rest, .. } => rest.is_some(),
        // Tuples are irrefutable if all elements are irrefutable.
        Pattern::Tuple(elems) => elems.iter().all(is_irrefutable_param),
        // An empty list pattern with a rest binding (`[..]` / `[..rest]`) matches
        // any list unconditionally.  Any other list pattern requires a specific
        // length, so it is refutable.
        Pattern::List { elements, rest } => elements.is_empty() && rest.is_some(),
        // Constructor and string-literal patterns are refutable.
        Pattern::Constructor { .. } | Pattern::StringLit(_) => false,
    }
}

/// Like `is_irrefutable_param` but used for `let` bindings, where any record
/// pattern is considered safe because the type system guarantees the value shape.
fn is_irrefutable_let(pat: &Pattern) -> bool {
    match pat {
        Pattern::Variable(..) | Pattern::Wildcard => true,
        // In let position the type system ensures the value has the right shape,
        // so both open and closed record patterns are unconditionally safe.
        Pattern::Record { .. } => true,
        Pattern::Tuple(elems) => elems.iter().all(is_irrefutable_let),
        Pattern::List { elements, rest } => elements.is_empty() && rest.is_some(),
        Pattern::Constructor { .. } | Pattern::StringLit(_) => false,
    }
}

/// Returns true if `p` is a catch-all pattern (no actual test at runtime).
fn pattern_is_catch_all(p: &Pattern) -> bool {
    match p {
        Pattern::Wildcard | Pattern::Variable(_, _) => true,
        Pattern::Record { .. } => true,
        Pattern::Tuple(elems) => elems.iter().all(pattern_is_catch_all),
        Pattern::List {
            elements,
            rest: Some(_),
        } => elements.is_empty(),
        _ => false,
    }
}

/// Returns `Some(name)` for concrete types that can name a trait dictionary,
/// or `None` for type variables and other unresolved types.
fn ty_target_name(ty: &Ty) -> Option<String> {
    match ty {
        Ty::F64 => Some("f64".to_string()),
        Ty::Con(name) => Some(name.clone()),
        Ty::App(con, _) => ty_target_name(con),
        _ => None,
    }
}

fn concrete_dict_name(trait_name: &str, ty: &Ty) -> Option<String> {
    ty_target_name(ty).map(|name| format!("__{}__{}", trait_name, name))
}

fn record_field_ty(ty: &Ty, field: &str) -> Option<Ty> {
    if let Ty::Record(row) = ty {
        row.fields
            .iter()
            .find(|(name, _)| name == field)
            .map(|(_, ty)| ty.clone())
    } else {
        None
    }
}

fn dict_param_name(constraint: &TraitConstraint) -> String {
    format!("__dict_{}_{}", constraint.trait_name, constraint.var)
}

fn attach_dict_args(
    dict_args: &mut Vec<String>,
    pending_dict_args: &mut Vec<PendingDictArg>,
    pending_constraints: &mut Vec<TraitConstraint>,
    constraints: &[TraitConstraint],
    subst: &Subst,
) {
    for constraint in constraints {
        let resolved = subst.apply(&Ty::Var(constraint.var));
        if let Some(dict_name) = concrete_dict_name(&constraint.trait_name, &resolved) {
            dict_args.push(dict_name);
        } else if let Ty::Var(var) = resolved {
            pending_constraints.push(TraitConstraint {
                var,
                trait_name: constraint.trait_name.clone(),
            });
            pending_dict_args.push(PendingDictArg {
                var,
                trait_name: constraint.trait_name.clone(),
            });
        } else {
            unreachable!("Resolved constraint target must be concrete or a type variable")
        }
    }
}

fn find_assignment_base_name(expr: &Expr) -> Option<String> {
    match &expr.kind {
        ExprKind::FieldAccess { expr, .. } => find_assignment_base_name(expr),
        ExprKind::Ident(name) => Some(name.clone()),
        _ => None,
    }
}

fn stmt_bound_names(stmt: &Stmt) -> CollectedNames {
    let mut names = CollectedNames::default();
    match stmt {
        Stmt::Let { pat, .. } => {
            insert_pattern_bindings(&mut names.values, pat);
        }
        Stmt::Fn { name, .. } | Stmt::Op { name, .. } | Stmt::Extern { name, .. } => {
            names.values.insert(name.clone());
        }
        Stmt::Type(td) => {
            names.types.insert(td.name.clone());
            names
                .values
                .extend(td.variants.iter().map(|variant| variant.name.clone()));
        }
        Stmt::TypeAlias { name, .. } => {
            names.types.insert(name.clone());
        }
        Stmt::Trait(_) | Stmt::Impl(_) | Stmt::Expr(_) => {}
    }
    names
}

fn stmt_referenced_names(stmt: &Stmt) -> CollectedNames {
    let mut refs = CollectedNames::default();
    collect_stmt_referenced_names(stmt, &mut refs, &HashSet::new(), &HashSet::new());
    refs
}

fn collect_stmt_referenced_names(
    stmt: &Stmt,
    refs: &mut CollectedNames,
    value_scope: &HashSet<String>,
    type_scope: &HashSet<String>,
) {
    match stmt {
        Stmt::Let { ty, value, .. } => {
            if let Some(ty) = ty {
                collect_type_referenced_names(ty, refs, type_scope);
            }
            collect_expr_referenced_names(value, refs, value_scope, type_scope);
        }
        Stmt::Fn {
            name,
            params,
            ret_type,
            body,
            ..
        } => {
            let mut body_scope = value_scope.clone();
            body_scope.insert(name.clone());
            for (pat, param_ty) in params {
                if let Some(param_ty) = param_ty {
                    collect_type_referenced_names(param_ty, refs, type_scope);
                }
                insert_pattern_bindings(&mut body_scope, pat);
            }
            if let Some(ret_type) = ret_type {
                collect_type_referenced_names(ret_type, refs, type_scope);
            }
            collect_expr_referenced_names(body, refs, &body_scope, type_scope);
        }
        Stmt::Op {
            params,
            ret_type,
            body,
            ..
        } => {
            let mut body_scope = value_scope.clone();
            for (pat, param_ty) in params {
                if let Some(param_ty) = param_ty {
                    collect_type_referenced_names(param_ty, refs, type_scope);
                }
                insert_pattern_bindings(&mut body_scope, pat);
            }
            if let Some(ret_type) = ret_type {
                collect_type_referenced_names(ret_type, refs, type_scope);
            }
            collect_expr_referenced_names(body, refs, &body_scope, type_scope);
        }
        Stmt::Trait(td) => {
            for method in &td.methods {
                for (_, param_ty) in &method.params {
                    collect_type_referenced_names(param_ty, refs, type_scope);
                }
                collect_type_referenced_names(&method.ret_type, refs, type_scope);
            }
        }
        Stmt::Impl(id) => {
            collect_type_referenced_names(&id.target, refs, type_scope);
            for method in &id.methods {
                let mut method_scope = value_scope.clone();
                for (pat, param_ty) in &method.params {
                    if let Some(param_ty) = param_ty {
                        collect_type_referenced_names(param_ty, refs, type_scope);
                    }
                    insert_pattern_bindings(&mut method_scope, pat);
                }
                if let Some(ret_type) = &method.ret_type {
                    collect_type_referenced_names(ret_type, refs, type_scope);
                }
                collect_expr_referenced_names(&method.body, refs, &method_scope, type_scope);
            }
        }
        Stmt::Type(td) => {
            let mut stmt_type_scope = type_scope.clone();
            stmt_type_scope.insert(td.name.clone());
            for variant in &td.variants {
                if let Some(payload) = &variant.payload {
                    collect_type_referenced_names(payload, refs, &stmt_type_scope);
                }
            }
        }
        Stmt::TypeAlias { name, ty, .. } => {
            let mut stmt_type_scope = type_scope.clone();
            stmt_type_scope.insert(name.clone());
            collect_type_referenced_names(ty, refs, &stmt_type_scope);
        }
        Stmt::Extern { ty, .. } => collect_type_referenced_names(ty, refs, type_scope),
        Stmt::Expr(expr) => collect_expr_referenced_names(expr, refs, value_scope, type_scope),
    }
}

fn collect_expr_referenced_names(
    expr: &Expr,
    refs: &mut CollectedNames,
    value_scope: &HashSet<String>,
    type_scope: &HashSet<String>,
) {
    match &expr.kind {
        ExprKind::Number(_)
        | ExprKind::StringLit(_)
        | ExprKind::Bool(_)
        | ExprKind::Import(_)
        | ExprKind::Unit
        | ExprKind::Break(None)
        | ExprKind::Continue
        | ExprKind::Return(None) => {}
        ExprKind::Ident(name) => {
            if !value_scope.contains(name) {
                refs.values.insert(name.clone());
            }
        }
        ExprKind::Not(expr)
        | ExprKind::Loop(expr)
        | ExprKind::Break(Some(expr))
        | ExprKind::Return(Some(expr))
        | ExprKind::FieldAccess { expr, .. } => {
            collect_expr_referenced_names(expr, refs, value_scope, type_scope);
        }
        ExprKind::Assign { target, value }
        | ExprKind::Binary {
            lhs: target,
            rhs: value,
            ..
        } => {
            collect_expr_referenced_names(target, refs, value_scope, type_scope);
            collect_expr_referenced_names(value, refs, value_scope, type_scope);
        }
        ExprKind::Call { callee, args, .. } => {
            collect_expr_referenced_names(callee, refs, value_scope, type_scope);
            for arg in args {
                collect_expr_referenced_names(arg, refs, value_scope, type_scope);
            }
        }
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
        } => {
            collect_expr_referenced_names(cond, refs, value_scope, type_scope);
            collect_expr_referenced_names(then_branch, refs, value_scope, type_scope);
            collect_expr_referenced_names(else_branch, refs, value_scope, type_scope);
        }
        ExprKind::Match { scrutinee, arms } => {
            collect_expr_referenced_names(scrutinee, refs, value_scope, type_scope);
            for (pattern, body) in arms {
                collect_pattern_referenced_names(pattern, refs);
                let mut arm_scope = value_scope.clone();
                insert_pattern_bindings(&mut arm_scope, pattern);
                collect_expr_referenced_names(body, refs, &arm_scope, type_scope);
            }
        }
        ExprKind::Block { stmts, final_expr } => {
            let mut block_value_scope = value_scope.clone();
            let mut block_type_scope = type_scope.clone();
            for stmt in stmts {
                collect_stmt_referenced_names(stmt, refs, &block_value_scope, &block_type_scope);
                let bindings = stmt_bound_names(stmt);
                block_value_scope.extend(bindings.values);
                block_type_scope.extend(bindings.types);
            }
            if let Some(expr) = final_expr {
                collect_expr_referenced_names(expr, refs, &block_value_scope, &block_type_scope);
            }
        }
        ExprKind::Tuple(items) => {
            for item in items {
                collect_expr_referenced_names(item, refs, value_scope, type_scope);
            }
        }
        ExprKind::Array(entries) => {
            for entry in entries {
                collect_expr_referenced_names(entry.expr(), refs, value_scope, type_scope);
            }
        }
        ExprKind::Record(entries) => {
            for entry in entries {
                collect_expr_referenced_names(entry.expr(), refs, value_scope, type_scope);
            }
        }
        ExprKind::Lambda { params, body, .. } => {
            let mut lambda_scope = value_scope.clone();
            for (pat, param_ty) in params {
                if let Some(param_ty) = param_ty {
                    collect_type_referenced_names(param_ty, refs, type_scope);
                }
                insert_pattern_bindings(&mut lambda_scope, pat);
            }
            collect_expr_referenced_names(body, refs, &lambda_scope, type_scope);
        }
        ExprKind::For {
            pat,
            iterable,
            body,
            ..
        } => {
            collect_expr_referenced_names(iterable, refs, value_scope, type_scope);
            collect_pattern_referenced_names(pat, refs);
            let mut body_scope = value_scope.clone();
            insert_pattern_bindings(&mut body_scope, pat);
            collect_expr_referenced_names(body, refs, &body_scope, type_scope);
        }
    }
}

fn collect_type_referenced_names(
    ty: &Type,
    refs: &mut CollectedNames,
    type_scope: &HashSet<String>,
) {
    match ty {
        Type::Ident(name) => {
            if !type_scope.contains(name) {
                refs.types.insert(name.clone());
            }
        }
        Type::App(con, args) => {
            collect_type_referenced_names(con, refs, type_scope);
            for arg in args {
                collect_type_referenced_names(arg, refs, type_scope);
            }
        }
        Type::Func(params, ret) => {
            for param in params {
                collect_type_referenced_names(param, refs, type_scope);
            }
            collect_type_referenced_names(ret, refs, type_scope);
        }
        Type::Tuple(items) => {
            for item in items {
                collect_type_referenced_names(item, refs, type_scope);
            }
        }
        Type::Record(fields, _) => {
            for (_, field_ty) in fields {
                collect_type_referenced_names(field_ty, refs, type_scope);
            }
        }
        Type::Var(_) | Type::Unit | Type::Hole => {}
    }
}

fn collect_pattern_referenced_names(pat: &Pattern, refs: &mut CollectedNames) {
    match pat {
        Pattern::Constructor { name, .. } => {
            refs.values.insert(name.clone());
        }
        Pattern::List { elements, .. } | Pattern::Tuple(elements) => {
            for element in elements {
                collect_pattern_referenced_names(element, refs);
            }
        }
        Pattern::Wildcard
        | Pattern::StringLit(_)
        | Pattern::Variable(_, _)
        | Pattern::Record { .. } => {}
    }
}

fn insert_pattern_bindings(scope: &mut HashSet<String>, pat: &Pattern) {
    match pat {
        Pattern::Wildcard | Pattern::StringLit(_) => {}
        Pattern::Variable(name, _) => {
            scope.insert(name.clone());
        }
        Pattern::Constructor { binding, .. } => {
            if let Some((binding, _)) = binding {
                scope.insert(binding.clone());
            }
        }
        Pattern::Record { fields, rest } => {
            for (_, binding, _) in fields {
                if binding != "_" {
                    scope.insert(binding.clone());
                }
            }
            if let Some(Some((rest_name, _))) = rest {
                scope.insert(rest_name.clone());
            }
        }
        Pattern::List { elements, rest } => {
            for element in elements {
                insert_pattern_bindings(scope, element);
            }
            if let Some(Some((rest_name, _))) = rest {
                scope.insert(rest_name.clone());
            }
        }
        Pattern::Tuple(elems) => {
            for elem in elems {
                insert_pattern_bindings(scope, elem);
            }
        }
    }
}

// ── Dict resolution helpers ───────────────────────────────────────────────────

fn resolve_local_dict_name(
    pending: &PendingDictArg,
    constraints: &[TraitConstraint],
    subst: &Subst,
) -> Option<String> {
    let resolved = subst.apply(&Ty::Var(pending.var));
    if let Ty::Var(var) = resolved {
        constraints
            .iter()
            .find(|c| c.var == var && c.trait_name == pending.trait_name)
            .map(dict_param_name)
    } else {
        None
    }
}

fn resolve_local_or_concrete(
    pending: &PendingDictArg,
    constraints: &[TraitConstraint],
    subst: &Subst,
) -> Option<String> {
    resolve_local_dict_name(pending, constraints, subst)
        .or_else(|| resolve_concrete(pending, subst))
}

fn resolve_concrete(pending: &PendingDictArg, subst: &Subst) -> Option<String> {
    concrete_dict_name(&pending.trait_name, &subst.apply(&Ty::Var(pending.var)))
}

// ── Dict-use resolution pass ──────────────────────────────────────────────────

/// Resolve all `pending_dict_args` / `pending_op` / `pending_iter` nodes in an
/// expression tree.
///
/// `resolve` maps a pending arg to a dict name (or `None` if not yet concrete).
/// `process_fn` controls whether `Stmt::Fn` / `Stmt::Op` inside block
/// expressions are recursed into — `false` during the per-function local pass
/// (those bodies are resolved by their own call), `true` during the global
/// final pass.
fn resolve_dict_uses_expr(
    expr: &mut Expr,
    resolve: &impl Fn(&PendingDictArg) -> Option<String>,
    process_fn: bool,
) -> Result<(), TypeError> {
    resolve_dict_uses_expr_with_mode(expr, resolve, process_fn, true)
}

fn resolve_dict_uses_expr_lenient(
    expr: &mut Expr,
    resolve: &impl Fn(&PendingDictArg) -> Option<String>,
    process_fn: bool,
) -> Result<(), TypeError> {
    resolve_dict_uses_expr_with_mode(expr, resolve, process_fn, false)
}

fn resolve_dict_uses_expr_with_mode(
    expr: &mut Expr,
    resolve: &impl Fn(&PendingDictArg) -> Option<String>,
    process_fn: bool,
    hard_unresolved: bool,
) -> Result<(), TypeError> {
    match &mut expr.kind {
        ExprKind::Binary {
            lhs,
            rhs,
            op,
            resolved_op,
            pending_op,
            dict_args,
            pending_dict_args,
            ..
        } => {
            if let BinOp::Custom(op_str) = op
                && let Some(pending) = pending_op.as_ref()
            {
                if let Some(dict_name) = resolve(pending) {
                    *resolved_op = Some(format!("{}.{}", dict_name, mangle_op(op_str)));
                    *pending_op = None;
                } else if hard_unresolved {
                    return Err(TypeError::UnresolvedTrait {
                        context: "operator".to_string(),
                        trait_name: pending.trait_name.clone(),
                    });
                }
            }
            if hard_unresolved {
                drain_pending(pending_dict_args, dict_args, "call", resolve)?;
            } else {
                drain_pending_lenient(pending_dict_args, dict_args, resolve);
            }
            resolve_dict_uses_expr_with_mode(lhs, resolve, process_fn, hard_unresolved)?;
            resolve_dict_uses_expr_with_mode(rhs, resolve, process_fn, hard_unresolved)?;
            Ok(())
        }
        ExprKind::Call {
            callee,
            args,
            arg_wrappers,
            dict_args,
            pending_dict_args,
            ..
        } => {
            if hard_unresolved {
                drain_pending(pending_dict_args, dict_args, "call", resolve)?;
            } else {
                drain_pending_lenient(pending_dict_args, dict_args, resolve);
            }
            for wrapper in arg_wrappers.iter_mut().flatten() {
                drain_pending_lenient(
                    &mut wrapper.pending_dict_args,
                    &mut wrapper.dict_args,
                    resolve,
                );
            }
            resolve_dict_uses_expr_with_mode(callee, resolve, process_fn, hard_unresolved)?;
            for arg in args {
                resolve_dict_uses_expr_with_mode(arg, resolve, process_fn, hard_unresolved)?;
            }
            Ok(())
        }
        ExprKind::Block { stmts, final_expr } => {
            for stmt in stmts {
                resolve_dict_uses_stmt_inner_with_mode(stmt, resolve, process_fn, hard_unresolved)?;
            }
            if let Some(e) = final_expr {
                resolve_dict_uses_expr_with_mode(e, resolve, process_fn, hard_unresolved)?;
            }
            Ok(())
        }
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
        } => {
            resolve_dict_uses_expr_with_mode(cond, resolve, process_fn, hard_unresolved)?;
            resolve_dict_uses_expr_with_mode(then_branch, resolve, process_fn, hard_unresolved)?;
            resolve_dict_uses_expr_with_mode(else_branch, resolve, process_fn, hard_unresolved)?;
            Ok(())
        }
        ExprKind::Lambda { body, .. } => {
            resolve_dict_uses_expr_with_mode(body, resolve, process_fn, hard_unresolved)
        }
        ExprKind::Match { scrutinee, arms } => {
            resolve_dict_uses_expr_with_mode(scrutinee, resolve, process_fn, hard_unresolved)?;
            for (_, arm_expr) in arms {
                resolve_dict_uses_expr_with_mode(arm_expr, resolve, process_fn, hard_unresolved)?;
            }
            Ok(())
        }
        ExprKind::Loop(body) => {
            resolve_dict_uses_expr_with_mode(body, resolve, process_fn, hard_unresolved)
        }
        ExprKind::Assign { target, value } => {
            resolve_dict_uses_expr_with_mode(target, resolve, process_fn, hard_unresolved)?;
            resolve_dict_uses_expr_with_mode(value, resolve, process_fn, hard_unresolved)?;
            Ok(())
        }
        ExprKind::Not(e) => {
            resolve_dict_uses_expr_with_mode(e, resolve, process_fn, hard_unresolved)
        }
        ExprKind::Break(Some(e)) | ExprKind::Return(Some(e)) => {
            resolve_dict_uses_expr_with_mode(e, resolve, process_fn, hard_unresolved)
        }
        ExprKind::Tuple(es) => {
            for e in es {
                resolve_dict_uses_expr_with_mode(e, resolve, process_fn, hard_unresolved)?;
            }
            Ok(())
        }
        ExprKind::Array(entries) => {
            for entry in entries {
                resolve_dict_uses_expr_with_mode(
                    entry.expr_mut(),
                    resolve,
                    process_fn,
                    hard_unresolved,
                )?;
            }
            Ok(())
        }
        ExprKind::Record(entries) => {
            for entry in entries {
                resolve_dict_uses_expr_with_mode(
                    entry.expr_mut(),
                    resolve,
                    process_fn,
                    hard_unresolved,
                )?;
            }
            Ok(())
        }
        ExprKind::FieldAccess { expr, .. } => {
            resolve_dict_uses_expr_with_mode(expr, resolve, process_fn, hard_unresolved)
        }
        ExprKind::For {
            iterable,
            body,
            resolved_iter,
            pending_iter,
            ..
        } => {
            if let Some(pending) = pending_iter.as_ref() {
                if let Some(dict_name) = resolve(pending) {
                    *resolved_iter = Some(format!("{}.iter", dict_name));
                    *pending_iter = None;
                } else if hard_unresolved {
                    return Err(TypeError::UnresolvedTrait {
                        context: "iterator".to_string(),
                        trait_name: pending.trait_name.clone(),
                    });
                }
            }
            resolve_dict_uses_expr_with_mode(iterable, resolve, process_fn, hard_unresolved)?;
            resolve_dict_uses_expr_with_mode(body, resolve, process_fn, hard_unresolved)?;
            Ok(())
        }
        ExprKind::Import(_) => Ok(()),
        _ => Ok(()),
    }
}

/// Stmt-level traversal shared by both passes. `process_fn` matches the same
/// flag as `resolve_dict_uses_expr`.
fn resolve_dict_uses_stmt_inner(
    stmt: &mut Stmt,
    resolve: &impl Fn(&PendingDictArg) -> Option<String>,
    process_fn: bool,
) -> Result<(), TypeError> {
    resolve_dict_uses_stmt_inner_with_mode(stmt, resolve, process_fn, true)
}

fn resolve_dict_uses_stmt_inner_with_mode(
    stmt: &mut Stmt,
    resolve: &impl Fn(&PendingDictArg) -> Option<String>,
    process_fn: bool,
    hard_unresolved: bool,
) -> Result<(), TypeError> {
    match stmt {
        Stmt::Fn { body, .. } | Stmt::Op { body, .. } => {
            if process_fn {
                resolve_dict_uses_expr_with_mode(body, resolve, process_fn, hard_unresolved)
            } else {
                Ok(()) // handled during that function's own inference
            }
        }
        Stmt::Let { value, .. } => {
            resolve_dict_uses_expr_with_mode(value, resolve, process_fn, hard_unresolved)
        }
        Stmt::Expr(e) => resolve_dict_uses_expr_with_mode(e, resolve, process_fn, hard_unresolved),
        Stmt::Impl(id) => {
            for method in &mut id.methods {
                resolve_dict_uses_expr_with_mode(
                    &mut method.body,
                    resolve,
                    process_fn,
                    hard_unresolved,
                )?;
            }
            Ok(())
        }
        _ => Ok(()),
    }
}

/// Final global pass: resolves remaining pending dict args using the fully
/// completed substitution. Called once per top-level statement after all
/// inference is done.
fn final_pass_stmt(
    stmt: &mut Stmt,
    resolve: &impl Fn(&PendingDictArg) -> Option<String>,
) -> Result<(), TypeError> {
    resolve_dict_uses_stmt_inner(stmt, resolve, true)
}

/// Drain `pending_dict_args` into `dict_args` using `resolve`, emitting an
/// error if a pending arg cannot be resolved.
fn drain_pending(
    pending: &mut Vec<PendingDictArg>,
    resolved: &mut Vec<String>,
    context: &str,
    resolve: &impl Fn(&PendingDictArg) -> Option<String>,
) -> Result<(), TypeError> {
    let names: Result<Vec<_>, _> = pending
        .iter()
        .map(|p| {
            resolve(p).ok_or_else(|| TypeError::UnresolvedTrait {
                context: context.to_string(),
                trait_name: p.trait_name.clone(),
            })
        })
        .collect();
    resolved.extend(names?);
    pending.clear();
    Ok(())
}

fn drain_pending_lenient(
    pending: &mut Vec<PendingDictArg>,
    resolved: &mut Vec<String>,
    resolve: &impl Fn(&PendingDictArg) -> Option<String>,
) {
    let mut unresolved = Vec::new();
    for item in pending.drain(..) {
        if let Some(name) = resolve(&item) {
            resolved.push(name);
        } else {
            unresolved.push(item);
        }
    }
    *pending = unresolved;
}

fn expr_always_exits(expr: &Expr, include_bc: bool) -> bool {
    match &expr.kind {
        ExprKind::Return(_) => true,
        ExprKind::Break(_) | ExprKind::Continue => include_bc,
        ExprKind::Not(e) | ExprKind::FieldAccess { expr: e, .. } => {
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
    fn syntactic_env_vars_are_normalized_before_constraint_partitioning() {
        let mut infer = Infer::new();
        let mut env = TypeEnv::new();
        env.insert(
            "outer".to_string(),
            EnvInfo {
                scheme: Scheme::mono(Ty::Var(0)),
                is_mutable: false,
            },
        );

        infer.subst.bind_ty(0, Ty::Var(1)).expect("valid alias");

        assert_eq!(
            infer.normalized_free_vars_syntactic(&env),
            HashSet::from([1])
        );
    }

    #[test]
    fn concrete_constraints_are_resolved_without_callable_dict_params() {
        let mut infer = Infer::new();
        infer
            .subst
            .bind_ty(0, Ty::F64)
            .expect("valid concrete type");

        let finalized = infer.finalize_constraints(
            &TypeEnv::new(),
            Ty::Func(vec![Ty::F64], Box::new(Ty::F64)),
            vec![TraitConstraint {
                var: 0,
                trait_name: "Add".to_string(),
            }],
        );

        assert!(finalized.owned.is_empty());
        assert!(finalized.bubbled.is_empty());
        assert!(finalized.scheme.constraints.is_empty());
    }
}
