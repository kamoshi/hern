//! Snapshots of mutable inference state.
//!
//! Recovery needs to try a declaration, keep useful metadata, and roll back
//! type-checking state when the declaration fails. This module captures the
//! pieces of `Infer` that participate in that rollback.

use super::metadata::{FailedStatementMetadata, TypeMetadataSnapshot};
use super::*;
use crate::types::SubstCheckpoint;

/// Snapshot of collecting-inference rollback state inside [`Infer`], taken before each
/// top-level statement and each statement inside a `test { ... }` block. On statement failure
/// the snapshot is restored so the next statement starts from a clean baseline.
///
/// Note: the substitution checkpoint restores solved substitutions, but not
/// `Subst::next_var`. Fresh type variable IDs keep advancing across recovery —
/// reusing IDs from a failed statement could alias new bindings against stale
/// references and silently miscompile.
///
/// Insert-only editor metadata maps keep only compact key lists here. Their keys are AST node IDs
/// or source spans, so a top-level statement should only add fresh keys; on rollback we turn those
/// lists into sets, retain entries that existed at the snapshot, and drop entries introduced by
/// the failed statement. Maps that can shadow user names still keep full snapshots below.
///
/// `variant_env` is intentionally omitted here: it is finalized before the main recovery loop,
/// and failed type declarations are pruned from it during pre-pass 3, so later statements never
/// observe variants from declarations whose constructor environment was discarded.
///
/// Rollback coverage checklist for `Infer` fields:
/// - captured here: substitutions, pending constraints, flow stacks, metadata, per-statement
///   import bindings, record-field callables, inherent methods, and the visible value environment;
/// - pre-pass/program declarations: traits, type aliases/declared names, impl dictionaries, and
///   scoped inherent methods are reset or rebuilt before collecting statements;
/// - session counters: `current_level` and `Subst::next_var` intentionally keep advancing.
pub(super) struct InferSnapshot {
    subst_checkpoint: SubstCheckpoint,
    constraints: ConstraintState,
    flow: FlowState,
    metadata: TypeMetadataSnapshot,
    import_bindings: HashMap<String, String>,
    record_field_callables: HashMap<String, HashMap<String, Vec<ParamCapability>>>,
    inherent_methods: HashMap<String, HashMap<String, InherentMethodInfo>>,
    env: TypeEnv,
}

impl InferSnapshot {
    pub(super) fn capture(infer: &Infer, env: &TypeEnv, subst_checkpoint: SubstCheckpoint) -> Self {
        Self {
            subst_checkpoint,
            constraints: infer.constraints.clone(),
            flow: infer.flow.clone(),
            metadata: infer.metadata.snapshot(),
            import_bindings: infer.imports.bindings.clone(),
            record_field_callables: infer.inherent.record_field_callables.clone(),
            inherent_methods: infer.inherent.methods.clone(),
            env: env.clone(),
        }
    }

    pub(super) fn metadata_added_before_failure(&self, infer: &Infer) -> FailedStatementMetadata {
        infer
            .metadata
            .metadata_added_after(&self.metadata, &infer.subst)
    }

    pub(super) fn restore(self, infer: &mut Infer, env: &mut TypeEnv) {
        infer.subst.restore_checkpoint(self.subst_checkpoint);
        infer.constraints = self.constraints;
        infer.flow = self.flow;
        infer.metadata.restore(self.metadata);
        infer.imports.bindings = self.import_bindings;
        infer.inherent.record_field_callables = self.record_field_callables;
        infer.inherent.methods = self.inherent_methods;
        *env = self.env;
    }

    pub(super) fn discard(self, infer: &mut Infer) {
        infer
            .subst
            .discard_outermost_checkpoint(self.subst_checkpoint);
    }
}
