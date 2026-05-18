//! Snapshots of mutable inference state.
//!
//! Recovery needs to try a declaration, keep useful metadata, and roll back
//! type-checking state when the declaration fails. This module captures the
//! pieces of `Infer` that participate in that rollback.

use super::metadata::{FailedStatementMetadata, TypeMetadataSnapshot};
use super::*;
use crate::types::SubstCheckpoint;

/// Snapshot of mutable per-statement state inside [`Infer`], taken before each top-level
/// statement during collecting inference. On statement failure the snapshot is restored so
/// the next statement starts from a clean baseline.
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
pub(super) struct InferSnapshot {
    subst_checkpoint: SubstCheckpoint,
    pending_constraints: Vec<TraitConstraint>,
    loop_break_tys: Vec<Ty>,
    fn_return_tys: Vec<FuncReturn>,
    metadata: TypeMetadataSnapshot,
    record_field_callables: HashMap<String, HashMap<String, Vec<ParamCapability>>>,
    inherent_methods: HashMap<String, HashMap<String, InherentMethodInfo>>,
    env: TypeEnv,
}

impl InferSnapshot {
    pub(super) fn capture(infer: &mut Infer, env: &TypeEnv) -> Self {
        Self {
            subst_checkpoint: infer.subst.checkpoint(),
            pending_constraints: infer.constraints.pending.clone(),
            loop_break_tys: infer.flow.loop_break_tys.clone(),
            fn_return_tys: infer.flow.fn_return_tys.clone(),
            metadata: infer.metadata.snapshot(),
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
        infer.constraints.pending = self.pending_constraints;
        infer.flow.loop_break_tys = self.loop_break_tys;
        infer.flow.fn_return_tys = self.fn_return_tys;
        infer.metadata.restore(self.metadata);
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
