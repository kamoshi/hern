#[cfg(feature = "perf-counters")]
mod imp {
    use std::env;
    use std::sync::OnceLock;
    use std::sync::atomic::{AtomicU64, Ordering};

    static ENABLED: OnceLock<bool> = OnceLock::new();

    static SUBST_APPLY_NODES: AtomicU64 = AtomicU64::new(0);
    static SUBST_SNAPSHOT_CALLS: AtomicU64 = AtomicU64::new(0);
    static SUBST_SNAPSHOT_ENTRIES: AtomicU64 = AtomicU64::new(0);
    static TYPE_ENV_FREE_VARS_CALLS: AtomicU64 = AtomicU64::new(0);
    static TYPE_ENV_FREE_VARS_ENTRIES: AtomicU64 = AtomicU64::new(0);
    static TYPE_ENV_APPLY_SUBST_CALLS: AtomicU64 = AtomicU64::new(0);
    static TYPE_ENV_APPLY_SUBST_ENTRIES: AtomicU64 = AtomicU64::new(0);
    static TYPE_ENV_APPLY_SUBST_CHANGED: AtomicU64 = AtomicU64::new(0);
    static FREE_TYPE_VARS_NODES: AtomicU64 = AtomicU64::new(0);
    static METADATA_FINALIZE_CALLS: AtomicU64 = AtomicU64::new(0);
    static METADATA_FINALIZE_ENTRIES: AtomicU64 = AtomicU64::new(0);
    static FRESH_PLACE_NODES: AtomicU64 = AtomicU64::new(0);
    static CARTESIAN_SEARCH_CALLS: AtomicU64 = AtomicU64::new(0);
    static CARTESIAN_SEARCH_LEAVES: AtomicU64 = AtomicU64::new(0);
    static MISSING_TYPE_LEVELS: AtomicU64 = AtomicU64::new(0);

    fn enabled() -> bool {
        *ENABLED.get_or_init(|| {
            env::var("HERN_PERF")
                .map(|value| value != "0" && !value.is_empty())
                .unwrap_or(false)
        })
    }

    fn inc(counter: &AtomicU64, value: u64) {
        if enabled() {
            counter.fetch_add(value, Ordering::Relaxed);
        }
    }

    pub(crate) fn subst_apply_node() {
        inc(&SUBST_APPLY_NODES, 1);
    }

    pub(crate) fn subst_snapshot(entries: usize) {
        inc(&SUBST_SNAPSHOT_CALLS, 1);
        inc(&SUBST_SNAPSHOT_ENTRIES, entries as u64);
    }

    pub(crate) fn type_env_free_vars(entries: usize) {
        inc(&TYPE_ENV_FREE_VARS_CALLS, 1);
        inc(&TYPE_ENV_FREE_VARS_ENTRIES, entries as u64);
    }

    pub(crate) fn type_env_apply_subst(entries: usize) {
        inc(&TYPE_ENV_APPLY_SUBST_CALLS, 1);
        inc(&TYPE_ENV_APPLY_SUBST_ENTRIES, entries as u64);
    }

    pub(crate) fn type_env_apply_subst_changed(entries: usize) {
        inc(&TYPE_ENV_APPLY_SUBST_CHANGED, entries as u64);
    }

    pub(crate) fn free_type_vars_node() {
        inc(&FREE_TYPE_VARS_NODES, 1);
    }

    pub(crate) fn metadata_finalize(entries: usize) {
        inc(&METADATA_FINALIZE_CALLS, 1);
        inc(&METADATA_FINALIZE_ENTRIES, entries as u64);
    }

    pub(crate) fn fresh_place_node() {
        inc(&FRESH_PLACE_NODES, 1);
    }

    pub(crate) fn cartesian_search_call() {
        inc(&CARTESIAN_SEARCH_CALLS, 1);
    }

    pub(crate) fn cartesian_search_leaf() {
        inc(&CARTESIAN_SEARCH_LEAVES, 1);
    }

    pub(crate) fn missing_type_level() {
        inc(&MISSING_TYPE_LEVELS, 1);
    }

    fn load(counter: &AtomicU64) -> u64 {
        counter.load(Ordering::Relaxed)
    }

    pub fn report() -> Option<String> {
        if !enabled() {
            return None;
        }
        Some(format!(
            "\
Hern perf counters:
  subst.apply node visits: {}
  subst snapshots: {} calls, {} total entries cloned
  type env free-vars: {} calls, {} total env entries scanned
  type env apply-subst: {} calls, {} total env entries scanned, {} entries changed
  free_type_vars node visits: {}
  metadata finalize: {} calls, {} total entries finalized
  fresh-place node visits: {}
  cartesian dict search: {} calls, {} leaves tried
  missing type levels: {}",
            load(&SUBST_APPLY_NODES),
            load(&SUBST_SNAPSHOT_CALLS),
            load(&SUBST_SNAPSHOT_ENTRIES),
            load(&TYPE_ENV_FREE_VARS_CALLS),
            load(&TYPE_ENV_FREE_VARS_ENTRIES),
            load(&TYPE_ENV_APPLY_SUBST_CALLS),
            load(&TYPE_ENV_APPLY_SUBST_ENTRIES),
            load(&TYPE_ENV_APPLY_SUBST_CHANGED),
            load(&FREE_TYPE_VARS_NODES),
            load(&METADATA_FINALIZE_CALLS),
            load(&METADATA_FINALIZE_ENTRIES),
            load(&FRESH_PLACE_NODES),
            load(&CARTESIAN_SEARCH_CALLS),
            load(&CARTESIAN_SEARCH_LEAVES),
            load(&MISSING_TYPE_LEVELS),
        ))
    }
}

#[cfg(not(feature = "perf-counters"))]
mod imp {
    pub(crate) fn subst_apply_node() {}
    pub(crate) fn subst_snapshot(_entries: usize) {}
    pub(crate) fn type_env_free_vars(_entries: usize) {}
    pub(crate) fn type_env_apply_subst(_entries: usize) {}
    pub(crate) fn type_env_apply_subst_changed(_entries: usize) {}
    pub(crate) fn free_type_vars_node() {}
    pub(crate) fn metadata_finalize(_entries: usize) {}
    pub(crate) fn fresh_place_node() {}
    pub(crate) fn cartesian_search_call() {}
    pub(crate) fn cartesian_search_leaf() {}
    pub(crate) fn missing_type_level() {}
    pub fn report() -> Option<String> {
        None
    }
}

pub(crate) use imp::{
    cartesian_search_call, cartesian_search_leaf, free_type_vars_node, fresh_place_node,
    metadata_finalize, missing_type_level, subst_apply_node, subst_snapshot, type_env_apply_subst,
    type_env_apply_subst_changed, type_env_free_vars,
};

pub use imp::report;
