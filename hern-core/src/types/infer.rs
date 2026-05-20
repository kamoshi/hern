//! Hindley-Milner style type inference for Hern programs.
//!
//! The root module owns the public inference API and the top-level program/statement
//! pipeline. Submodules are split by type-system responsibility: expression forms,
//! scoped inference state, schemes, trait dictionaries, impl/declaration checking,
//! and the metadata/recovery passes that make inference useful to callers.

mod aggregates;
mod calls;
mod decls;
mod dicts;
mod exprs;
mod funcs;
mod impls;
mod indexing;
mod iteration;
mod lexical;
mod macro_phase;
mod metadata;
mod operators;
mod pattern_infer;
mod rec_blocks;
mod recovery;
mod schemes;
mod scopes;
mod snapshot;
mod state;
mod test_blocks;
mod ty_helpers;
mod type_convert;
mod walkers;

use self::dicts::{
    attach_dict_args, dict_param_name, dict_ref_concrete_name, final_pass_stmt, resolve_concrete,
    resolve_concrete_dict_ref, resolve_concrete_from_args_unifying, resolve_dict_uses_expr,
    resolve_dict_uses_expr_lenient, resolve_local_or_concrete,
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
use crate::lex::NumberLiteral;
use crate::types::{
    BindingCapabilities, CallableCapabilities, EnvInfo, FuncParam, FuncReturn,
    InherentMethodScheme, ParamCapability, ROOT_LEVEL, ReturnCapability, Row, Scheme, Subst,
    SyntaxCaptureInfo, TraitConstraint, Ty, TyVar, TypeLevel, display_ty_with_var_names,
    env::build_variant_env_from_stmts,
    error::{
        MutablePlaceErrorReason, MutablePlaceSubject, SpannedTypeError, TypeError,
        TypeMismatchContext,
    },
    free_type_vars, free_type_vars_in_display_order, free_type_vars_into, perf, type_var_name,
    unify, value_func_params, value_func_return,
};
pub use crate::types::{TypeEnv, VariantEnv, VariantInfo, is_fresh_mutable_place, is_value};
#[cfg(debug_assertions)]
use std::sync::OnceLock;

use aggregates::*;
use funcs::*;
use metadata::{FinalizedTypeMaps, NO_NODE_ID, TypeMetadata};
use rec_blocks::*;
use recovery::{CollectedNames, stmt_bound_names, stmt_referenced_names};
use snapshot::InferSnapshot;
use state::*;
use std::collections::{HashMap, HashSet};
use ty_helpers::*;
use walkers::*;

#[derive(Debug, Clone)]
struct InherentMethodInfo {
    scheme: Scheme,
    resolved_callee: ResolvedCallee,
    has_receiver: bool,
}

// ── Infer ─────────────────────────────────────────────────────────────────────

pub struct Infer {
    subst: Subst,
    traits: TraitScope,
    types: TypeScope,
    imports: ImportScope,
    inherent: InherentScope,
    impls: ImplScope,
    flow: FlowState,
    constraints: ConstraintState,
    metadata: TypeMetadata,
    current_level: TypeLevel,
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
    pub syntax_captures: HashMap<SourceSpan, SyntaxCaptureInfo>,
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
            syntax_captures: HashMap::new(),
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
            traits: TraitScope::default(),
            types: TypeScope::default(),
            imports: ImportScope::default(),
            inherent: InherentScope::default(),
            impls: ImplScope::default(),
            flow: FlowState::default(),
            constraints: ConstraintState::default(),
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

    pub fn set_import_types(&mut self, import_types: HashMap<String, Ty>) {
        self.imports.types = import_types;
    }

    pub fn set_import_schemes(&mut self, import_schemes: HashMap<String, HashMap<String, Scheme>>) {
        self.imports.schemes = import_schemes;
    }

    pub fn set_known_impl_dicts(&mut self, dicts: HashSet<String>) {
        self.impls.active_dicts = dicts.clone();
        self.impls.scoped_dicts = dicts;
    }

    pub fn set_known_impl_schemes(&mut self, schemes: HashMap<String, Scheme>) {
        self.impls.known_schemes = schemes;
    }

    pub fn set_trait_scope(
        &mut self,
        traits: HashMap<String, TraitDef>,
        op_trait_map: HashMap<String, String>,
    ) {
        self.traits.env = traits.clone();
        self.traits.scoped_env = traits;
        self.traits.op_trait_map = op_trait_map.clone();
        self.traits.scoped_op_trait_map = op_trait_map;
    }

    pub fn set_type_scope(&mut self, type_names: HashSet<String>) {
        self.types.scoped_declared = type_names;
    }

    pub fn set_inherent_scope(
        &mut self,
        inherent_methods: HashMap<String, HashMap<String, InherentMethodScheme>>,
    ) {
        self.inherent.scoped_methods = inherent_methods
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
        let module_name = self.imports.bindings.get(base_name)?;
        self.imports
            .schemes
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
            return Err(TypeError::ExpectedMutablePlace {
                subject: MutablePlaceSubject::Argument(idx + 1),
                reason: MutablePlaceErrorReason::NotAPlace,
            }
            .at(arg.span));
        };
        let info = env
            .get(&name)
            .ok_or_else(|| TypeError::UnboundVariable(name.clone()).at(arg.span))?;
        if info.is_place_mutable() {
            Ok(())
        } else {
            Err(TypeError::ExpectedMutablePlace {
                subject: MutablePlaceSubject::Argument(idx + 1),
                reason: MutablePlaceErrorReason::NotMutable(name),
            }
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

    fn apply_env_subst(&self, env: &mut TypeEnv) {
        env.apply_subst(&self.subst);
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
        self.types.variant_env = build_variant_env_from_stmts(seed_stmts, &program.stmts);

        let mut env = seed_env.cloned().unwrap_or_else(TypeEnv::new);
        self.validate_type_trait_name_collisions(seed_stmts, &program.stmts)?;
        if let Some(err) = self
            .validate_duplicate_test_function_names(&program.stmts)
            .into_iter()
            .next()
        {
            return Err(err);
        }
        self.register_type_declarations(seed_stmts.iter().chain(program.stmts.iter()))?;
        self.resolve_registered_variant_payload_types();
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
                    &self.impls.active_dicts,
                    &self.impls.known_schemes,
                    &self.subst,
                )
            };
            final_pass_stmt(stmt, &resolver)?;
        }

        let maps = self.finalized_type_maps();

        Ok(InferenceResult {
            env,
            variant_env: self.types.variant_env.clone(),
            inherent_method_schemes: self.export_inherent_method_schemes(),
            value_ty: self.subst.apply(&value_ty),
            expr_types: maps.expr_types,
            symbol_types: maps.symbol_types,
            binding_types: maps.binding_types,
            syntax_captures: maps.syntax_captures,
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
    /// - Pre-pass 1 (type/type alias registry) is fail-fast: malformed generic
    ///   parameters would corrupt later alias/type conversion, so a single
    ///   accurate diagnostic beats partial-recovery noise.
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
        self.types.variant_env = build_variant_env_from_stmts(seed_stmts, &program.stmts);

        let mut env = seed_env.cloned().unwrap_or_else(TypeEnv::new);
        if let Err(err) = self.validate_type_trait_name_collisions(seed_stmts, &program.stmts) {
            return (ModuleInference::default(), vec![err]);
        }
        let duplicate_test_name_errors =
            self.validate_duplicate_test_function_names(&program.stmts);
        if let Err(err) =
            self.register_type_declarations(seed_stmts.iter().chain(program.stmts.iter()))
        {
            let mut diagnostics = duplicate_test_name_errors;
            diagnostics.push(err);
            return (ModuleInference::default(), diagnostics);
        }
        self.resolve_registered_variant_payload_types();
        if let Err(err) =
            self.register_traits_and_ops(seed_stmts.iter().chain(program.stmts.iter()))
        {
            let mut diagnostics = duplicate_test_name_errors;
            diagnostics.push(err);
            return (ModuleInference::default(), diagnostics);
        }
        // Collecting inference returns partial state after failures, so current-module
        // impl dictionaries must become visible only after their impl statement succeeds.
        // Module-scope discovery may have preloaded them into active dictionaries; remove
        // only this program's impl names while preserving imported/prelude impls.
        self.remove_program_impl_dict_names(program.stmts.iter());

        let mut diagnostics: Vec<SpannedTypeError> = duplicate_test_name_errors;
        let mut unavailable = CollectedNames::default();

        self.add_constructors_and_externs_collecting(
            &mut env,
            &mut program.stmts,
            &mut unavailable,
            &mut diagnostics,
        );

        let (value_ty, succeeded) = self.infer_top_level_statements_collecting(
            &mut env,
            &mut program.stmts,
            &mut unavailable,
            &mut diagnostics,
        );

        self.apply_env_subst(&mut env);
        self.final_pass_succeeded_statements_collecting(
            &env,
            &mut program.stmts,
            &succeeded,
            &mut diagnostics,
        );

        let maps = self.finalized_type_maps();

        (
            ModuleInference {
                env,
                variant_env: self.types.variant_env.clone(),
                inherent_method_schemes: self.export_inherent_method_schemes(),
                value_ty: self.subst.apply(&value_ty),
                expr_types: maps.expr_types,
                symbol_types: maps.symbol_types,
                binding_types: maps.binding_types,
                syntax_captures: maps.syntax_captures,
                definition_schemes: maps.definition_schemes,
                binding_capabilities: maps.binding_capabilities,
                callable_capabilities: maps.callable_capabilities,
                fresh_place_exprs: maps.fresh_place_exprs,
            },
            diagnostics,
        )
    }

    fn add_constructors_and_externs_collecting(
        &mut self,
        env: &mut TypeEnv,
        stmts: &mut [Stmt],
        unavailable: &mut CollectedNames,
        diagnostics: &mut Vec<SpannedTypeError>,
    ) {
        for stmt in stmts {
            let span = stmt.span();
            let bound = stmt_bound_names(stmt);
            match stmt {
                Stmt::Type(td) => {
                    if let Err(err) = self.add_constructors_to_env(env, td) {
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
                            let scheme = self.generalize_at(env, t, ambient);
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
    }

    fn infer_top_level_statements_collecting(
        &mut self,
        env: &mut TypeEnv,
        stmts: &mut [Stmt],
        unavailable: &mut CollectedNames,
        diagnostics: &mut Vec<SpannedTypeError>,
    ) -> (Ty, Vec<bool>) {
        let mut value_ty = Ty::Unit;
        let mut succeeded = vec![false; stmts.len()];
        for (idx, stmt) in stmts.iter_mut().enumerate() {
            let bound = stmt_bound_names(stmt);
            let refs = stmt_referenced_names(stmt);
            if matches!(stmt, Stmt::Type(_) | Stmt::Extern { .. }) && unavailable.overlaps(&bound) {
                continue;
            }
            if unavailable.overlaps(&refs) {
                unavailable.extend(bound);
                continue;
            }

            if let Stmt::TestBlock { stmts, .. } = stmt {
                let block_diagnostics = self.infer_test_block_collecting(env, stmts);
                let block_ok = block_diagnostics.is_empty();
                diagnostics.extend(block_diagnostics);
                succeeded[idx] = block_ok;
                value_ty = Ty::Unit;
                continue;
            }

            let subst_checkpoint = self.subst.checkpoint();
            let snapshot = InferSnapshot::capture(self, env, subst_checkpoint);

            match self.infer_stmt(env, stmt) {
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
                    snapshot.restore(self, env);
                    // Keep callee metadata discovered before the error so LSP hover and
                    // signature help can still explain bad calls in a failed statement.
                    self.metadata.extend_failed_statement(failed_metadata);
                    unavailable.extend(bound);
                    diagnostics.push(err);
                }
            }
        }
        (value_ty, succeeded)
    }

    fn final_pass_succeeded_statements_collecting(
        &mut self,
        env: &TypeEnv,
        stmts: &mut [Stmt],
        succeeded: &[bool],
        diagnostics: &mut Vec<SpannedTypeError>,
    ) {
        for (stmt, &ok) in stmts.iter_mut().zip(succeeded.iter()) {
            if !ok {
                continue;
            }
            let span = stmt.span();
            let resolver = |p: &PendingDictArg| {
                resolve_concrete(
                    p,
                    env,
                    &self.impls.active_dicts,
                    &self.impls.known_schemes,
                    &self.subst,
                )
            };
            if let Err(err) = final_pass_stmt(stmt, &resolver) {
                diagnostics.push(err.at(span));
            }
        }
    }

    fn reset_program_state(&mut self) {
        self.subst.clear_map_keep_counter();
        self.types.reset_for_program();
        self.traits.reset_for_program();
        self.impls.reset_for_program();
        self.inherent.methods.clear();
        self.constraints.clear();
        self.flow.clear();
        self.metadata.clear();
        self.imports.bindings.clear();
        self.inherent.record_field_callables.clear();
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
                let env_vars_before_let = if generalizable_value {
                    env.free_vars(&self.subst)
                } else {
                    HashSet::new()
                };
                let pending_start = self.constraints.pending.len();
                let inferred_ty = if generalizable_value {
                    self.with_child_level(|this| this.infer_let_value_ty(env, ty, value))?
                } else {
                    self.infer_let_value_ty(env, ty, value)?
                };
                // A value that creates a pending trait constraint over an existing
                // environment variable cannot soundly own that dictionary in a
                // polymorphic scheme. Keep the binding monomorphic so the outer
                // scope resolves the exact captured dictionary use.
                let captures_constraint_from_env = generalizable_value && {
                    let env_vars_after_let = env.free_vars(&self.subst);
                    self.constraints.pending[pending_start..]
                        .iter()
                        .any(|constraint| {
                            constraint_mentions_any_var(
                                constraint,
                                &env_vars_after_let,
                                &self.subst,
                            )
                        })
                };

                // Reject refutable patterns in let position.
                if !is_irrefutable_let(pat, &self.types.variant_env) {
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
                    } else if !generalizable_value || captures_constraint_from_env {
                        Scheme::mono(inferred_ty)
                    } else {
                        self.generalize_at(env, inferred_ty, ambient)
                    };
                    let place_mutable = *is_mutable && self.is_fresh_mutable_place_expr(value);
                    self.metadata
                        .record_binding_capability(*span, BindingCapabilities { place_mutable });
                    if let ExprKind::Import(path) = &value.kind {
                        self.imports.bindings.insert(name.clone(), path.clone());
                    } else if let Some(fields) = self.record_literal_callable_fields(value) {
                        self.inherent
                            .record_field_callables
                            .insert(name.clone(), fields);
                    } else if let ExprKind::Ident(source_name) = &value.kind
                        && let Some(fields) = self
                            .inherent
                            .record_field_callables
                            .get(source_name)
                            .cloned()
                    {
                        self.inherent
                            .record_field_callables
                            .insert(name.clone(), fields);
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
                    // Destructuring: bind each pattern variable, then generalize
                    // against the pre-let environment so sibling bindings don't
                    // prevent each other from being generalized.
                    self.check_pattern(pat, inferred_ty, env, *is_mutable)?;
                    if generalizable_value && !captures_constraint_from_env {
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
                                ty_vars.difference(&env_vars_before_let).copied().collect();
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
                    false,
                )?;
                Ok(Ty::Unit)
            }
            Stmt::Macro(def) => {
                self.infer_macro_defs(env, std::slice::from_mut(def))?;
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
            Stmt::TestBlock { stmts, .. } => {
                let mut test_env = env.clone();
                for stmt in stmts.iter_mut() {
                    self.infer_stmt(&mut test_env, stmt)?;
                    self.validate_test_stmt_shape(&test_env, stmt)?;
                }
                Ok(Ty::Unit)
            }
            Stmt::RecBlock { stmts, .. } => {
                self.infer_rec_block(env, stmts)?;
                Ok(Ty::Unit)
            }
            Stmt::Expr(expr) => self.infer_expr(env, expr),
        })();
        result.map_err(|err| match stmt {
            Stmt::Impl(ImplDef {
                generated_by:
                    Some(GeneratedBy::Derive {
                        trait_name,
                        source_span,
                    }),
                ..
            }) => {
                let mut err = err.with_span_if_absent_or_synthetic(*source_span);
                err.error = Box::new(TypeError::DerivedImplFailure {
                    trait_name: trait_name.clone(),
                    error: err.error,
                });
                err
            }
            _ => err.with_span_if_absent(span),
        })
    }
}

#[cfg(test)]
mod tests;
