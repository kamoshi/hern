//! Grouped state carried by the inference engine.
//!
//! `Infer` has several lifetimes of state: session-wide trait knowledge,
//! program-scoped declarations/imports, impl dictionaries, flow stacks, and
//! pending constraints. Grouping fields makes resets and snapshots reflect those
//! type-system roles directly.

use super::*;

#[derive(Default)]
pub(super) struct TraitScope {
    pub(super) env: HashMap<String, TraitDef>,
    pub(super) op_trait_map: HashMap<String, String>,
}

#[derive(Default)]
pub(super) struct TypeScope {
    pub(super) variant_env: VariantEnv,
    pub(super) aliases: HashMap<String, (Vec<String>, Type)>,
    pub(super) declared: HashSet<String>,
    pub(super) scoped_declared: HashSet<String>,
}

#[derive(Default)]
pub(super) struct ImportScope {
    pub(super) types: HashMap<String, Ty>,
    pub(super) schemes: HashMap<String, HashMap<String, Scheme>>,
    pub(super) bindings: HashMap<String, String>,
}

#[derive(Default)]
pub(super) struct InherentScope {
    pub(super) methods: HashMap<String, HashMap<String, InherentMethodInfo>>,
    pub(super) scoped_methods: HashMap<String, HashMap<String, InherentMethodInfo>>,
    pub(super) record_field_callables: HashMap<String, HashMap<String, Vec<ParamCapability>>>,
}

#[derive(Default)]
pub(super) struct ImplScope {
    pub(super) known_dicts: HashSet<String>,
    pub(super) known_schemes: HashMap<String, Scheme>,
}

#[derive(Default)]
pub(super) struct FlowState {
    pub(super) loop_break_tys: Vec<Ty>,
    pub(super) fn_return_tys: Vec<FuncReturn>,
}

#[derive(Default)]
pub(super) struct ConstraintState {
    pub(super) pending: Vec<TraitConstraint>,
}
