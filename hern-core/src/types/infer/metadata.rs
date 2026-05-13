use super::*;
use std::hash::Hash;

#[derive(Default)]
pub(super) struct TypeMetadata {
    expr_types: HashMap<NodeId, Ty>,
    symbol_types: HashMap<NodeId, Ty>,
    binding_types: HashMap<SourceSpan, Ty>,
    definition_schemes: HashMap<SourceSpan, Scheme>,
    binding_capabilities: HashMap<SourceSpan, BindingCapabilities>,
    callable_capabilities: HashMap<NodeId, CallableCapabilities>,
    fresh_place_exprs: HashSet<NodeId>,
}

pub(super) struct FinalizedTypeMaps {
    pub(super) expr_types: HashMap<NodeId, Ty>,
    pub(super) symbol_types: HashMap<NodeId, Ty>,
    pub(super) binding_types: HashMap<SourceSpan, Ty>,
    pub(super) definition_schemes: HashMap<SourceSpan, Scheme>,
    pub(super) binding_capabilities: HashMap<SourceSpan, BindingCapabilities>,
    pub(super) callable_capabilities: HashMap<NodeId, CallableCapabilities>,
    pub(super) fresh_place_exprs: HashSet<NodeId>,
}

pub(super) struct FailedStatementMetadata {
    pub(super) symbol_types: HashMap<NodeId, Ty>,
    pub(super) callable_capabilities: HashMap<NodeId, CallableCapabilities>,
}

pub(super) struct TypeMetadataSnapshot {
    expr_type_keys: Vec<NodeId>,
    symbol_type_keys: Vec<NodeId>,
    binding_type_keys: Vec<SourceSpan>,
    definition_scheme_keys: Vec<SourceSpan>,
    binding_capability_keys: Vec<SourceSpan>,
    callable_capability_keys: Vec<NodeId>,
    fresh_place_expr_keys: Vec<NodeId>,
}

impl TypeMetadata {
    pub(super) fn clear(&mut self) {
        self.expr_types.clear();
        self.symbol_types.clear();
        self.binding_types.clear();
        self.definition_schemes.clear();
        self.binding_capabilities.clear();
        self.callable_capabilities.clear();
        self.fresh_place_exprs.clear();
    }

    pub(super) fn record_expr_type(&mut self, node_id: NodeId, ty: Ty) {
        if node_id != NO_NODE_ID {
            self.expr_types.insert(node_id, ty);
        }
    }

    pub(super) fn record_symbol_type(&mut self, node_id: NodeId, ty: Ty) {
        if node_id != NO_NODE_ID {
            self.symbol_types.insert(node_id, ty);
        }
    }

    pub(super) fn record_binding_type(&mut self, span: SourceSpan, ty: Ty) {
        self.binding_types.insert(span, ty);
    }

    pub(super) fn record_definition_scheme(&mut self, span: SourceSpan, scheme: Scheme) {
        self.definition_schemes.insert(span, scheme);
    }

    pub(super) fn record_binding_capability(
        &mut self,
        span: SourceSpan,
        capability: BindingCapabilities,
    ) {
        self.binding_capabilities.insert(span, capability);
    }

    pub(super) fn record_callable_capabilities(
        &mut self,
        node_id: NodeId,
        param_capabilities: Vec<ParamCapability>,
    ) {
        if node_id != NO_NODE_ID {
            self.callable_capabilities
                .insert(node_id, CallableCapabilities { param_capabilities });
        }
    }

    pub(super) fn callable_capabilities_for(&self, node_id: NodeId) -> Vec<ParamCapability> {
        self.callable_capabilities
            .get(&node_id)
            .map(|capabilities| capabilities.param_capabilities.clone())
            .unwrap_or_default()
    }

    pub(super) fn callable_capabilities(&self, node_id: NodeId) -> Option<&CallableCapabilities> {
        self.callable_capabilities.get(&node_id)
    }

    pub(super) fn mark_fresh_place(&mut self, node_id: NodeId) {
        if node_id != NO_NODE_ID {
            self.fresh_place_exprs.insert(node_id);
        }
    }

    pub(super) fn is_fresh_place_expr(&self, node_id: NodeId) -> bool {
        self.fresh_place_exprs.contains(&node_id)
    }

    pub(super) fn extend_failed_statement(&mut self, failed: FailedStatementMetadata) {
        self.symbol_types.extend(failed.symbol_types);
        self.callable_capabilities
            .extend(failed.callable_capabilities);
    }

    pub(super) fn finalize(&self, subst: &Subst) -> FinalizedTypeMaps {
        perf::metadata_finalize(
            self.expr_types.len()
                + self.symbol_types.len()
                + self.binding_types.len()
                + self.definition_schemes.len(),
        );
        FinalizedTypeMaps {
            expr_types: self
                .expr_types
                .iter()
                .map(|(id, ty)| (*id, subst.apply(ty)))
                .collect(),
            symbol_types: self
                .symbol_types
                .iter()
                .map(|(id, ty)| (*id, subst.apply(ty)))
                .collect(),
            binding_types: self
                .binding_types
                .iter()
                .map(|(span, ty)| (*span, subst.apply(ty)))
                .collect(),
            definition_schemes: self
                .definition_schemes
                .iter()
                .map(|(span, scheme)| (*span, subst.apply_scheme(scheme)))
                .collect(),
            binding_capabilities: self.binding_capabilities.clone(),
            callable_capabilities: self.callable_capabilities.clone(),
            fresh_place_exprs: self.fresh_place_exprs.clone(),
        }
    }

    pub(super) fn snapshot(&self) -> TypeMetadataSnapshot {
        TypeMetadataSnapshot {
            expr_type_keys: self.expr_types.keys().copied().collect(),
            symbol_type_keys: self.symbol_types.keys().copied().collect(),
            binding_type_keys: self.binding_types.keys().copied().collect(),
            definition_scheme_keys: self.definition_schemes.keys().copied().collect(),
            binding_capability_keys: self.binding_capabilities.keys().copied().collect(),
            callable_capability_keys: self.callable_capabilities.keys().copied().collect(),
            fresh_place_expr_keys: self.fresh_place_exprs.iter().copied().collect(),
        }
    }

    pub(super) fn metadata_added_after(
        &self,
        snapshot: &TypeMetadataSnapshot,
        subst: &Subst,
    ) -> FailedStatementMetadata {
        let symbol_type_keys: HashSet<_> = snapshot.symbol_type_keys.iter().copied().collect();
        let callable_capability_keys: HashSet<_> =
            snapshot.callable_capability_keys.iter().copied().collect();
        FailedStatementMetadata {
            symbol_types: self
                .symbol_types
                .iter()
                .filter(|(id, _)| !symbol_type_keys.contains(id))
                .map(|(id, ty)| (*id, subst.apply(ty)))
                .collect(),
            callable_capabilities: self
                .callable_capabilities
                .iter()
                .filter(|(id, _)| !callable_capability_keys.contains(id))
                .map(|(id, capabilities)| (*id, capabilities.clone()))
                .collect(),
        }
    }

    pub(super) fn restore(&mut self, snapshot: TypeMetadataSnapshot) {
        retain_map_keys(&mut self.expr_types, snapshot.expr_type_keys);
        retain_map_keys(&mut self.symbol_types, snapshot.symbol_type_keys);
        retain_map_keys(&mut self.binding_types, snapshot.binding_type_keys);
        retain_map_keys(
            &mut self.definition_schemes,
            snapshot.definition_scheme_keys,
        );
        retain_map_keys(
            &mut self.binding_capabilities,
            snapshot.binding_capability_keys,
        );
        retain_map_keys(
            &mut self.callable_capabilities,
            snapshot.callable_capability_keys,
        );
        retain_set_keys(&mut self.fresh_place_exprs, snapshot.fresh_place_expr_keys);
    }
}

fn retain_map_keys<K, V>(map: &mut HashMap<K, V>, snapshot_keys: Vec<K>)
where
    K: Eq + Hash,
{
    let snapshot_keys: HashSet<_> = snapshot_keys.into_iter().collect();
    map.retain(|key, _| snapshot_keys.contains(key));
}

fn retain_set_keys<K>(set: &mut HashSet<K>, snapshot_keys: Vec<K>)
where
    K: Eq + Hash,
{
    let snapshot_keys: HashSet<_> = snapshot_keys.into_iter().collect();
    set.retain(|key| snapshot_keys.contains(key));
}
