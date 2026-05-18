mod env;
pub mod error;
pub mod infer;
mod patterns;
pub mod perf;
pub(crate) mod type_syntax;
mod value;

pub use env::{TypeEnv, VariantEnv, VariantInfo};
pub use type_syntax::{
    inherent_impl_target_keys_from_ty, trait_dict_indexes, trait_impl_arg_key_candidates_from_ty,
    trait_impl_arg_keys_from_ast, trait_impl_arg_keys_from_ty, trait_impl_args_key_from_ast,
    trait_impl_dict_name, trait_impl_dict_name_for_indexes, trait_impl_dict_name_from_keys,
    trait_impl_target_key_from_ast, trait_impl_target_keys_from_ty,
};
pub use value::{is_fresh_mutable_place, is_value};

use std::collections::{HashMap, HashSet};
use std::fmt;
use std::sync::OnceLock;

use error::TypeMismatchContext;

pub type TyVar = u32;
pub type TypeLevel = u32;
pub const ROOT_LEVEL: TypeLevel = 0;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct TraitConstraint {
    /// Compatibility dispatch variable for existing unary trait machinery.
    /// For multi-parameter traits this is the primary unresolved variable used
    /// for dictionary parameter naming; `args` carries the full predicate.
    pub var: TyVar,
    pub trait_name: String,
    pub args: Vec<Ty>,
    pub determinant_indexes: Vec<usize>,
}

impl TraitConstraint {
    pub fn unary(var: TyVar, trait_name: impl Into<String>) -> Self {
        Self {
            var,
            trait_name: trait_name.into(),
            args: vec![Ty::Var(var)],
            determinant_indexes: vec![0],
        }
    }

    pub fn predicate(
        trait_name: impl Into<String>,
        args: Vec<Ty>,
        primary_var: TyVar,
        determinant_indexes: Vec<usize>,
    ) -> Self {
        debug_assert!(
            determinant_indexes_are_prefix(&determinant_indexes),
            "source fundep arrows currently split a prefix determinant list"
        );
        Self {
            var: primary_var,
            trait_name: trait_name.into(),
            args,
            determinant_indexes,
        }
    }
}

pub fn determinant_indexes_are_prefix(indexes: &[usize]) -> bool {
    indexes.iter().copied().eq(0..indexes.len())
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Ty {
    Int,
    Float,
    Unit,
    Never,
    Qualified(Vec<TraitConstraint>, Box<Ty>),
    Tuple(Vec<Ty>),
    Func(Vec<FuncParam>, FuncReturn),
    Var(TyVar),
    /// A concrete type constructor: `bool`, `Array`, `Option`
    Con(String),
    /// Type application: `Array[float]`, `Map[string, int]`
    App(Box<Ty>, Vec<Ty>),
    Record(Row),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct FuncParam {
    pub ty: Ty,
    pub capability: ParamCapability,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct FuncReturn {
    pub ty: Box<Ty>,
    pub capability: ReturnCapability,
}

impl FuncParam {
    pub fn value(ty: Ty) -> Self {
        Self {
            ty,
            capability: ParamCapability::Value,
        }
    }

    pub fn mut_place(ty: Ty) -> Self {
        Self {
            ty,
            capability: ParamCapability::MutPlace,
        }
    }
}

impl FuncReturn {
    pub fn value(ty: Ty) -> Self {
        Self {
            ty: Box::new(ty),
            capability: ReturnCapability::Value,
        }
    }

    pub fn fresh_place(ty: Ty) -> Self {
        Self {
            ty: Box::new(ty),
            capability: ReturnCapability::FreshPlace,
        }
    }
}

pub fn value_func_params(params: Vec<Ty>) -> Vec<FuncParam> {
    params.into_iter().map(FuncParam::value).collect()
}

pub fn value_func_return(ret: Ty) -> FuncReturn {
    FuncReturn::value(ret)
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Row {
    pub fields: Vec<(String, Ty)>,
    pub tail: Box<Ty>,
}

impl fmt::Display for Ty {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // No naming context here: Ty::Var renders as the raw numeric ID.
        // Scheme::Display uses DisplayTy with a populated map for pretty 'a/'b output.
        DisplayTy(self, empty_tyvar_names()).fmt(f)
    }
}

/// Converts a 0-based scheme-variable index to a human-readable lowercase letter name
/// using bijective base-26: 0→"a", 25→"z", 26→"aa", 701→"zz", 702→"aaa", …
///
/// The algorithm is correct for all `usize` values; there is no upper bound.
pub fn type_var_name(index: usize) -> String {
    const LETTERS: &[u8] = b"abcdefghijklmnopqrstuvwxyz";
    let mut buf = Vec::new();
    let mut n = index;
    loop {
        buf.push(LETTERS[n % 26]);
        if n < 26 {
            break;
        }
        n = (n / 26) - 1;
    }
    buf.reverse();
    String::from_utf8(buf).expect("ASCII letters only")
}

fn empty_tyvar_names() -> &'static HashMap<TyVar, String> {
    static EMPTY: OnceLock<HashMap<TyVar, String>> = OnceLock::new();
    EMPTY.get_or_init(HashMap::new)
}

/// Displays a `Ty` using a caller-supplied naming context that maps `TyVar` IDs to
/// human-readable letters (e.g. `'a`, `'b`). Used by `Scheme`'s `Display` impl.
///
/// `Ty`'s own `Display` delegates here with an empty map, so raw numeric IDs appear
/// in standalone type display (e.g. in error messages). That is intentional: a bare
/// `Ty` has no scheme context to assign meaningful names from.
#[derive(Clone, Copy)]
struct DisplayTy<'a>(&'a Ty, &'a HashMap<TyVar, String>);

impl fmt::Display for DisplayTy<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let (ty, names) = (self.0, self.1);
        match ty {
            Ty::Int => write!(f, "int"),
            Ty::Float => write!(f, "float"),
            Ty::Unit => write!(f, "()"),
            Ty::Never => write!(f, "!"),
            Ty::Var(v) => match names.get(v) {
                Some(name) => write!(f, "'{}", name),
                None => write!(f, "'{}", v),
            },
            Ty::Con(name) => write!(f, "{}", name),
            Ty::Qualified(constraints, inner) => {
                write!(f, "[")?;
                for (i, c) in constraints.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", DisplayTraitConstraint(c, names))?;
                }
                write!(f, "] {}", DisplayTy(inner, names))
            }
            Ty::App(con, args) => {
                if let Ty::Con(name) = &**con
                    && name == "Array"
                    && args.len() == 1
                {
                    return write!(f, "[{}]", DisplayTy(&args[0], names));
                }
                write!(f, "{}(", DisplayTy(con, names))?;
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", DisplayTy(arg, names))?;
                }
                write!(f, ")")
            }
            Ty::Tuple(tys) => {
                write!(f, "(")?;
                for (i, t) in tys.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", DisplayTy(t, names))?;
                }
                write!(f, ")")
            }
            Ty::Func(params, ret) => {
                write!(f, "fn(")?;
                for (i, p) in params.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    if p.capability.is_mut_place() {
                        write!(f, "mut ")?;
                    }
                    write!(f, "{}", DisplayTy(&p.ty, names))?;
                }
                write!(f, ") -> ")?;
                if ret.capability == ReturnCapability::FreshPlace {
                    write!(f, "mut ")?;
                }
                write!(f, "{}", DisplayTy(&ret.ty, names))
            }
            Ty::Record(row) => {
                // Pre-render each field value so we can decide on layout before
                // writing anything.  Multiline layout is used when:
                //   • there are 4+ fields, OR
                //   • any field value is itself multiline (nested large record), OR
                //   • the inline rendering would exceed ~80 characters.
                let rendered: Vec<(&str, String)> = row
                    .fields
                    .iter()
                    .map(|(name, ty)| (name.as_str(), DisplayTy(ty, names).to_string()))
                    .collect();

                let inline_len: usize = rendered
                    .iter()
                    .map(|(k, v)| k.len() + 2 + v.len()) // "key: value"
                    .sum::<usize>()
                    + rendered.len().saturating_sub(1) * 2 // ", " separators
                    + 4; // "#{ " + " }"

                let multiline = rendered.len() >= 4
                    || rendered.iter().any(|(_, v)| v.contains('\n'))
                    || inline_len > 80;

                if multiline {
                    writeln!(f, "#{{ ")?;
                    for (name, rendered_ty) in &rendered {
                        writeln!(f, "  {}: {},", name, rendered_ty)?;
                    }
                    match &*row.tail {
                        Ty::Unit => {}
                        Ty::Var(v) => match names.get(v) {
                            Some(name) => writeln!(f, "  ..'{},", name)?,
                            None => writeln!(f, "  ..'{},", v)?,
                        },
                        _ => writeln!(f, "  ..{},", DisplayTy(&row.tail, names))?,
                    }
                    write!(f, "}}")
                } else {
                    write!(f, "#{{ ")?;
                    for (i, (name, rendered_ty)) in rendered.iter().enumerate() {
                        if i > 0 {
                            write!(f, ", ")?;
                        }
                        write!(f, "{}: {}", name, rendered_ty)?;
                    }
                    match &*row.tail {
                        Ty::Unit => {}
                        Ty::Var(v) => match names.get(v) {
                            Some(name) => write!(f, ", ..'{}", name)?,
                            None => write!(f, ", ..'{}", v)?,
                        },
                        _ => write!(f, ", ..{}", DisplayTy(&row.tail, names))?,
                    }
                    write!(f, " }}")
                }
            }
        }
    }
}

pub fn display_ty_with_var_names(ty: &Ty, names: &HashMap<TyVar, String>) -> String {
    DisplayTy(ty, names).to_string()
}

pub fn free_type_vars_in_display_order(ty: &Ty) -> Vec<TyVar> {
    fn collect(ty: &Ty, vars: &mut Vec<TyVar>) {
        match ty {
            Ty::Var(var) => {
                if !vars.contains(var) {
                    vars.push(*var);
                }
            }
            Ty::Qualified(constraints, inner) => {
                collect(inner, vars);
                for constraint in constraints {
                    if !vars.contains(&constraint.var) {
                        vars.push(constraint.var);
                    }
                    for arg in &constraint.args {
                        collect(arg, vars);
                    }
                }
            }
            Ty::Tuple(items) => {
                for item in items {
                    collect(item, vars);
                }
            }
            Ty::Func(params, ret) => {
                for param in params {
                    collect(&param.ty, vars);
                }
                collect(&ret.ty, vars);
            }
            Ty::App(con, args) => {
                collect(con, vars);
                for arg in args {
                    collect(arg, vars);
                }
            }
            Ty::Record(row) => {
                for (_, ty) in &row.fields {
                    collect(ty, vars);
                }
                collect(&row.tail, vars);
            }
            Ty::Int | Ty::Float | Ty::Unit | Ty::Never | Ty::Con(_) => {}
        }
    }

    let mut vars = Vec::new();
    collect(ty, &mut vars);
    vars
}

#[derive(Debug, Clone)]
pub struct Scheme {
    pub vars: Vec<TyVar>,
    pub constraints: Vec<TraitConstraint>,
    pub ty: Ty,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ParamCapability {
    Value,
    MutPlace,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ReturnCapability {
    Value,
    FreshPlace,
}

impl ParamCapability {
    pub fn is_mut_place(self) -> bool {
        matches!(self, ParamCapability::MutPlace)
    }
}

#[derive(Debug, Clone, Default)]
pub struct BindingCapabilities {
    pub place_mutable: bool,
}

#[derive(Debug, Clone, Default)]
pub struct CallableCapabilities {
    pub param_capabilities: Vec<ParamCapability>,
}

#[derive(Debug, Clone)]
pub struct InherentMethodScheme {
    pub scheme: Scheme,
    pub has_receiver: bool,
}

impl fmt::Display for Scheme {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.vars.is_empty() {
            write!(f, "{}", self.ty)
        } else {
            // Assign human-readable letters to bound type variables in declaration order.
            let names: HashMap<TyVar, String> = self
                .vars
                .iter()
                .enumerate()
                .map(|(i, &v)| (v, type_var_name(i)))
                .collect();

            write!(f, "∀")?;
            for v in &self.vars {
                write!(f, " '{}", names[v])?;
            }
            if !self.constraints.is_empty() {
                write!(f, " [")?;
                for (i, c) in self.constraints.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", DisplayTraitConstraint(c, &names))?;
                }
                write!(f, "]")?;
            }
            write!(f, ". {}", DisplayTy(&self.ty, &names))
        }
    }
}

struct DisplayTraitConstraint<'a>(&'a TraitConstraint, &'a HashMap<TyVar, String>);

impl fmt::Display for DisplayTraitConstraint<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let (constraint, names) = (self.0, self.1);
        if matches!(constraint.args.as_slice(), [Ty::Var(var)] if *var == constraint.var) {
            return match names.get(&constraint.var) {
                Some(name) => write!(f, "'{}: {}", name, constraint.trait_name),
                None => write!(f, "'{}: {}", constraint.var, constraint.trait_name),
            };
        }

        write!(f, "{}[", constraint.trait_name)?;
        let determinant_count = constraint.determinant_indexes.len();
        for (idx, arg) in constraint.args.iter().enumerate() {
            if idx > 0 {
                if idx == determinant_count {
                    write!(f, " -> ")?;
                } else {
                    write!(f, ", ")?;
                }
            }
            write!(f, "{}", DisplayTy(arg, names))?;
        }
        write!(f, "]")
    }
}

impl Scheme {
    pub fn mono(ty: Ty) -> Self {
        Self {
            vars: vec![],
            constraints: vec![],
            ty,
        }
    }
}

#[derive(Debug, Clone)]
pub struct EnvInfo {
    pub scheme: Scheme,
    pub binding_mutable: bool,
    pub place_mutable: bool,
}

impl EnvInfo {
    pub fn immutable(scheme: Scheme) -> Self {
        Self {
            scheme,
            binding_mutable: false,
            place_mutable: false,
        }
    }

    pub fn mutable_binding(scheme: Scheme) -> Self {
        Self {
            scheme,
            binding_mutable: true,
            place_mutable: false,
        }
    }

    pub fn mutable_place(scheme: Scheme) -> Self {
        Self {
            scheme,
            binding_mutable: true,
            place_mutable: true,
        }
    }

    pub fn with_place_mutable(mut self, place_mutable: bool) -> Self {
        self.place_mutable = place_mutable;
        self
    }

    pub fn is_binding_mutable(&self) -> bool {
        self.binding_mutable
    }

    pub fn is_place_mutable(&self) -> bool {
        self.place_mutable
    }
}

#[derive(Clone)]
pub struct Subst {
    map: HashMap<TyVar, Ty>,
    levels: HashMap<TyVar, TypeLevel>,
    next_var: TyVar,
    journal: Vec<SubstJournalEntry>,
    active_checkpoints: usize,
}

#[derive(Clone)]
enum SubstJournalEntry {
    Binding { var: TyVar, previous: Option<Ty> },
    Level { var: TyVar, previous: TypeLevel },
}

#[derive(Clone, Copy)]
pub(crate) struct SubstCheckpoint {
    journal_len: usize,
    depth: usize,
}

impl Default for Subst {
    fn default() -> Self {
        Self::new()
    }
}

impl Subst {
    pub fn new() -> Self {
        Self {
            map: HashMap::new(),
            levels: HashMap::new(),
            next_var: 0,
            journal: Vec::new(),
            active_checkpoints: 0,
        }
    }

    /// Allocate a fresh type variable ID without wrapping it in `Ty::Var`.
    pub fn fresh_tyvar(&mut self) -> TyVar {
        self.fresh_tyvar_at(ROOT_LEVEL)
    }

    pub fn fresh_tyvar_at(&mut self, level: TypeLevel) -> TyVar {
        let v = self.next_var;
        self.next_var += 1;
        self.levels.insert(v, level);
        v
    }

    pub fn level_of(&self, var: TyVar) -> TypeLevel {
        self.levels.get(&var).copied().unwrap_or_else(|| {
            perf::missing_type_level();
            ROOT_LEVEL
        })
    }

    pub(crate) fn set_level(&mut self, var: TyVar, level: TypeLevel) {
        self.levels.insert(var, level);
    }

    /// Snapshots the unification map so a caller can roll back the substitution after a
    /// failed inference attempt while leaving the fresh-variable counter intact.
    pub fn snapshot_map(&self) -> HashMap<TyVar, Ty> {
        perf::subst_snapshot(self.map.len());
        self.map.clone()
    }

    /// Restores a previously [`snapshot_map`]ped substitution. Does not touch `next_var`,
    /// so fresh variables allocated since the snapshot remain accounted for.
    pub fn restore_map(&mut self, map: HashMap<TyVar, Ty>) {
        self.map = map;
        self.journal.clear();
        self.active_checkpoints = 0;
    }

    /// Creates a lightweight rollback marker for speculative inference.
    ///
    /// Unlike [`snapshot_map`], this does not clone the substitution map. Mutations
    /// after the checkpoint are recorded by [`bind_ty`] and can be rolled back by
    /// replaying the journal in reverse.
    pub(crate) fn checkpoint(&mut self) -> SubstCheckpoint {
        perf::subst_snapshot(0);
        let checkpoint = SubstCheckpoint {
            journal_len: self.journal.len(),
            depth: self.active_checkpoints,
        };
        self.active_checkpoints += 1;
        checkpoint
    }

    pub(crate) fn restore_checkpoint(&mut self, checkpoint: SubstCheckpoint) {
        assert_eq!(
            self.active_checkpoints,
            checkpoint.depth + 1,
            "substitution checkpoints must be restored in LIFO order"
        );
        while self.journal.len() > checkpoint.journal_len {
            let entry = self
                .journal
                .pop()
                .expect("journal length checked before pop");
            match entry {
                SubstJournalEntry::Binding { var, previous } => match previous {
                    Some(previous) => {
                        self.map.insert(var, previous);
                    }
                    None => {
                        self.map.remove(&var);
                    }
                },
                SubstJournalEntry::Level { var, previous } => {
                    self.levels.insert(var, previous);
                }
            }
        }
        self.active_checkpoints = checkpoint.depth;
    }

    /// Discards rollback history for a successful outer inference scope while
    /// keeping its substitutions.
    ///
    /// Nested speculative checkpoints must be restored instead. Dropping their
    /// journal entries while an older checkpoint is still active would make the
    /// older rollback incomplete.
    pub(crate) fn discard_outermost_checkpoint(&mut self, checkpoint: SubstCheckpoint) {
        assert_eq!(
            checkpoint.journal_len, 0,
            "only the outer collecting-inference checkpoint may be discarded"
        );
        assert_eq!(
            checkpoint.depth, 0,
            "discard_outermost_checkpoint requires the outermost checkpoint"
        );
        assert_eq!(
            self.active_checkpoints, 1,
            "discard_outermost_checkpoint requires no nested active checkpoints"
        );
        self.journal.clear();
        self.active_checkpoints = 0;
    }

    /// Clears solved substitutions while preserving the fresh-variable counter.
    ///
    /// Graph inference calls this between finalized modules. Exported environments and editor
    /// metadata are fully substituted before they leave a module, but keeping `next_var` monotonic
    /// avoids reusing IDs that may still appear in exported polymorphic schemes.
    pub fn clear_map_keep_counter(&mut self) {
        self.map.clear();
        self.levels.clear();
        self.journal.clear();
        self.active_checkpoints = 0;
    }

    /// Allocate a fresh type variable wrapped as `Ty::Var`.
    pub fn fresh_var(&mut self) -> Ty {
        Ty::Var(self.fresh_tyvar())
    }

    pub fn apply(&self, ty: &Ty) -> Ty {
        perf::subst_apply_node();
        match ty {
            Ty::Var(v) => {
                if let Some(t) = self.map.get(v) {
                    self.apply(t)
                } else {
                    Ty::Var(*v)
                }
            }
            Ty::Qualified(constraints, ty) => Ty::Qualified(
                constraints
                    .iter()
                    .filter_map(|c| {
                        let args = c.args.iter().map(|arg| self.apply(arg)).collect::<Vec<_>>();
                        let var = match self.apply(&Ty::Var(c.var)) {
                            Ty::Var(var) => Some(var),
                            // Fully concrete qualified predicates cannot stay as
                            // `TraitConstraint` values because constraints are keyed
                            // by a dispatch type variable. Concrete obligations are
                            // resolved before this normalization path; if no argument
                            // still carries a variable, the predicate has no generic
                            // dictionary parameter left to preserve.
                            _ => args.iter().find_map(first_type_var),
                        }?;
                        Some(TraitConstraint {
                            var,
                            trait_name: c.trait_name.clone(),
                            args,
                            determinant_indexes: c.determinant_indexes.clone(),
                        })
                    })
                    .collect(),
                Box::new(self.apply(ty)),
            ),
            Ty::Func(params, ret) => Ty::Func(
                params
                    .iter()
                    .map(|p| FuncParam {
                        ty: self.apply(&p.ty),
                        capability: p.capability,
                    })
                    .collect(),
                FuncReturn {
                    ty: Box::new(self.apply(&ret.ty)),
                    capability: ret.capability,
                },
            ),
            Ty::Tuple(tys) => Ty::Tuple(tys.iter().map(|t| self.apply(t)).collect()),
            Ty::App(con, args) => Ty::App(
                Box::new(self.apply(con)),
                args.iter().map(|a| self.apply(a)).collect(),
            ),
            Ty::Record(row) => {
                let mut fields = Vec::new();
                for (n, t) in &row.fields {
                    fields.push((n.clone(), self.apply(t)));
                }
                let tail = self.apply(&row.tail);
                if let Ty::Record(inner_row) = tail {
                    fields.extend(inner_row.fields);
                    sort_record_fields(&mut fields);
                    Ty::Record(Row {
                        fields,
                        tail: inner_row.tail,
                    })
                } else {
                    sort_record_fields(&mut fields);
                    Ty::Record(Row {
                        fields,
                        tail: Box::new(tail),
                    })
                }
            }
            t => t.clone(),
        }
    }

    pub(crate) fn would_change(&self, ty: &Ty) -> bool {
        match ty {
            Ty::Var(v) => self.map.contains_key(v),
            Ty::Qualified(constraints, ty) => {
                constraints.iter().any(|constraint| {
                    self.map.contains_key(&constraint.var)
                        || constraint.args.iter().any(|arg| self.would_change(arg))
                }) || self.would_change(ty)
            }
            Ty::Func(params, ret) => {
                params.iter().any(|param| self.would_change(&param.ty))
                    || self.would_change(&ret.ty)
            }
            Ty::Tuple(tys) => tys.iter().any(|ty| self.would_change(ty)),
            Ty::App(con, args) => {
                self.would_change(con) || args.iter().any(|arg| self.would_change(arg))
            }
            Ty::Record(row) => {
                !record_fields_sorted(&row.fields)
                    || matches!(&*row.tail, Ty::Record(_))
                    || row.fields.iter().any(|(_, ty)| self.would_change(ty))
                    || self.would_change(&row.tail)
            }
            Ty::Int | Ty::Float | Ty::Unit | Ty::Never | Ty::Con(_) => false,
        }
    }

    pub(crate) fn free_vars_after_apply_into(&self, ty: &Ty, vars: &mut HashSet<TyVar>) {
        perf::free_type_vars_node();
        match ty {
            Ty::Var(v) => {
                if let Some(ty) = self.map.get(v) {
                    self.free_vars_after_apply_into(ty, vars);
                } else {
                    vars.insert(*v);
                }
            }
            Ty::Qualified(constraints, ty) => {
                self.free_vars_after_apply_into(ty, vars);
                for constraint in constraints {
                    if let Ty::Var(var) = self.apply(&Ty::Var(constraint.var)) {
                        vars.insert(var);
                    }
                    for arg in &constraint.args {
                        self.free_vars_after_apply_into(arg, vars);
                    }
                }
            }
            Ty::Func(params, ret) => {
                for param in params {
                    self.free_vars_after_apply_into(&param.ty, vars);
                }
                self.free_vars_after_apply_into(&ret.ty, vars);
            }
            Ty::Tuple(tys) => {
                for ty in tys {
                    self.free_vars_after_apply_into(ty, vars);
                }
            }
            Ty::App(con, args) => {
                self.free_vars_after_apply_into(con, vars);
                for arg in args {
                    self.free_vars_after_apply_into(arg, vars);
                }
            }
            Ty::Record(row) => {
                for (_, ty) in &row.fields {
                    self.free_vars_after_apply_into(ty, vars);
                }
                self.free_vars_after_apply_into(&row.tail, vars);
            }
            Ty::Int | Ty::Float | Ty::Unit | Ty::Never | Ty::Con(_) => {}
        }
    }

    pub fn apply_scheme(&self, scheme: &Scheme) -> Scheme {
        Scheme {
            vars: scheme.vars.clone(),
            constraints: scheme.constraints.clone(),
            ty: self.apply(&scheme.ty),
        }
    }

    pub fn bind_ty(&mut self, v: TyVar, t: Ty) -> Result<(), error::TypeError> {
        let t = self.apply(&t);
        if let Ty::Var(v2) = t
            && v == v2
        {
            return Ok(());
        }
        if type_contains_var(&t, v) {
            if option_type_contains_var(&t, v) {
                return Err(error::TypeError::Mismatch {
                    expected: t,
                    got: Ty::Var(v),
                });
            }
            return Err(error::TypeError::OccursCheck(v));
        }
        let target_level = self
            .min_level_in_ty(&t)
            .map(|level| self.level_of(v).min(level))
            .unwrap_or_else(|| self.level_of(v));
        self.lower_var_level(v, target_level);
        self.lower_levels_in_ty(&t, target_level);
        if self.active_checkpoints > 0 {
            self.journal.push(SubstJournalEntry::Binding {
                var: v,
                previous: self.map.get(&v).cloned(),
            });
        }
        self.map.insert(v, t);
        Ok(())
    }

    fn min_level_in_ty(&self, ty: &Ty) -> Option<TypeLevel> {
        match ty {
            // If a variable is already substituted, the binding itself carries
            // the meaningful levels. A fully concrete binding contributes no
            // nested level, so the variable's recorded level is the conservative
            // floor for the outer binding.
            Ty::Var(var) => self
                .map
                .get(var)
                .and_then(|ty| self.min_level_in_ty(ty))
                .or_else(|| Some(self.level_of(*var))),
            Ty::Qualified(constraints, inner) => constraints
                .iter()
                .flat_map(|constraint| {
                    std::iter::once(Some(self.level_of(constraint.var)))
                        .chain(constraint.args.iter().map(|arg| self.min_level_in_ty(arg)))
                })
                .chain(std::iter::once(self.min_level_in_ty(inner)))
                .flatten()
                .min(),
            Ty::Func(params, ret) => params
                .iter()
                .map(|param| self.min_level_in_ty(&param.ty))
                .chain(std::iter::once(self.min_level_in_ty(&ret.ty)))
                .flatten()
                .min(),
            Ty::Tuple(tys) => tys.iter().filter_map(|ty| self.min_level_in_ty(ty)).min(),
            Ty::App(con, args) => std::iter::once(self.min_level_in_ty(con))
                .chain(args.iter().map(|arg| self.min_level_in_ty(arg)))
                .flatten()
                .min(),
            Ty::Record(row) => row
                .fields
                .iter()
                .map(|(_, ty)| self.min_level_in_ty(ty))
                .chain(std::iter::once(self.min_level_in_ty(&row.tail)))
                .flatten()
                .min(),
            Ty::Int | Ty::Float | Ty::Unit | Ty::Never | Ty::Con(_) => None,
        }
    }

    fn lower_levels_in_ty(&mut self, ty: &Ty, target: TypeLevel) {
        match ty {
            Ty::Var(var) => {
                if let Some(ty) = self.map.get(var).cloned() {
                    self.lower_levels_in_ty(&ty, target);
                } else {
                    self.lower_var_level(*var, target);
                }
            }
            Ty::Qualified(constraints, inner) => {
                self.lower_levels_in_ty(inner, target);
                for constraint in constraints {
                    self.lower_var_level(constraint.var, target);
                    for arg in &constraint.args {
                        self.lower_levels_in_ty(arg, target);
                    }
                }
            }
            Ty::Func(params, ret) => {
                for param in params {
                    self.lower_levels_in_ty(&param.ty, target);
                }
                self.lower_levels_in_ty(&ret.ty, target);
            }
            Ty::Tuple(tys) => {
                for ty in tys {
                    self.lower_levels_in_ty(ty, target);
                }
            }
            Ty::App(con, args) => {
                self.lower_levels_in_ty(con, target);
                for arg in args {
                    self.lower_levels_in_ty(arg, target);
                }
            }
            Ty::Record(row) => {
                for (_, ty) in &row.fields {
                    self.lower_levels_in_ty(ty, target);
                }
                self.lower_levels_in_ty(&row.tail, target);
            }
            Ty::Int | Ty::Float | Ty::Unit | Ty::Never | Ty::Con(_) => {}
        }
    }

    fn lower_var_level(&mut self, var: TyVar, target: TypeLevel) {
        let old = self.level_of(var);
        if target < old {
            if self.active_checkpoints > 0 {
                self.journal
                    .push(SubstJournalEntry::Level { var, previous: old });
            }
            self.set_level(var, target);
        }
    }
}

fn record_fields_sorted(fields: &[(String, Ty)]) -> bool {
    fields.windows(2).all(|pair| pair[0].0 <= pair[1].0)
}

fn sort_record_fields(fields: &mut [(String, Ty)]) {
    if !record_fields_sorted(fields) {
        fields.sort_by(|(a, _), (b, _)| a.cmp(b));
    }
}

fn type_contains_var(ty: &Ty, needle: TyVar) -> bool {
    match ty {
        Ty::Var(v) => *v == needle,
        Ty::Qualified(constraints, ty) => {
            constraints.iter().any(|constraint| {
                constraint.var == needle
                    || constraint
                        .args
                        .iter()
                        .any(|arg| type_contains_var(arg, needle))
            }) || type_contains_var(ty, needle)
        }
        Ty::Func(params, ret) => {
            params
                .iter()
                .any(|param| type_contains_var(&param.ty, needle))
                || type_contains_var(&ret.ty, needle)
        }
        Ty::Tuple(tys) => tys.iter().any(|ty| type_contains_var(ty, needle)),
        Ty::App(con, args) => {
            type_contains_var(con, needle) || args.iter().any(|arg| type_contains_var(arg, needle))
        }
        Ty::Record(row) => {
            row.fields
                .iter()
                .any(|(_, ty)| type_contains_var(ty, needle))
                || type_contains_var(&row.tail, needle)
        }
        Ty::Int | Ty::Float | Ty::Unit | Ty::Never | Ty::Con(_) => false,
    }
}

fn first_type_var(ty: &Ty) -> Option<TyVar> {
    match ty {
        Ty::Var(var) => Some(*var),
        Ty::Qualified(constraints, inner) => constraints
            .iter()
            .find_map(|constraint| constraint.args.iter().find_map(first_type_var))
            .or_else(|| first_type_var(inner)),
        Ty::Func(params, ret) => params
            .iter()
            .find_map(|param| first_type_var(&param.ty))
            .or_else(|| first_type_var(&ret.ty)),
        Ty::Tuple(items) => items.iter().find_map(first_type_var),
        Ty::App(con, args) => first_type_var(con).or_else(|| args.iter().find_map(first_type_var)),
        Ty::Record(row) => row
            .fields
            .iter()
            .find_map(|(_, ty)| first_type_var(ty))
            .or_else(|| first_type_var(&row.tail)),
        Ty::Int | Ty::Float | Ty::Unit | Ty::Never | Ty::Con(_) => None,
    }
}

fn option_type_contains_var(ty: &Ty, needle: TyVar) -> bool {
    match ty {
        Ty::App(con, args)
            if matches!(con.as_ref(), Ty::Con(name) if name == "Option")
                && args.iter().any(|arg| type_contains_var(arg, needle)) =>
        {
            true
        }
        Ty::Qualified(_, inner) => option_type_contains_var(inner, needle),
        _ => false,
    }
}

pub fn free_type_vars(ty: &Ty) -> HashSet<TyVar> {
    let mut vars = HashSet::new();
    free_type_vars_into(ty, &mut vars);
    vars
}

pub fn free_type_vars_into(ty: &Ty, vars: &mut HashSet<TyVar>) {
    perf::free_type_vars_node();
    match ty {
        Ty::Var(v) => {
            vars.insert(*v);
        }
        Ty::Qualified(constraints, ty) => {
            free_type_vars_into(ty, vars);
            for constraint in constraints {
                vars.insert(constraint.var);
                for arg in &constraint.args {
                    free_type_vars_into(arg, vars);
                }
            }
        }
        Ty::Func(params, ret) => {
            for p in params {
                free_type_vars_into(&p.ty, vars);
            }
            free_type_vars_into(&ret.ty, vars);
        }
        Ty::Tuple(tys) => {
            for t in tys {
                free_type_vars_into(t, vars);
            }
        }
        Ty::App(con, args) => {
            free_type_vars_into(con, vars);
            for a in args {
                free_type_vars_into(a, vars);
            }
        }
        Ty::Record(row) => {
            for (_, t) in &row.fields {
                free_type_vars_into(t, vars);
            }
            free_type_vars_into(&row.tail, vars);
        }
        _ => {}
    }
}

/// Unifies two plain monotypes.
///
/// `Ty::Qualified` carries dictionary obligations and must be handled by the
/// inference layer that can preserve or reject those constraints. Treating a
/// qualified type as its inner type here would silently erase required evidence.
/// The first argument is the actual type and the second is the expected type in
/// diagnostics.
pub fn unify(s: &mut Subst, t1: Ty, t2: Ty) -> Result<(), error::TypeError> {
    let t1 = s.apply(&t1);
    let t2 = s.apply(&t2);

    match (t1, t2) {
        (Ty::Int, Ty::Int) | (Ty::Float, Ty::Float) | (Ty::Unit, Ty::Unit) => Ok(()),
        (Ty::Never, Ty::Never) => Ok(()),
        (Ty::Con(n1), Ty::Con(n2)) if n1 == n2 => Ok(()),
        (Ty::Var(v), t) | (t, Ty::Var(v)) => s.bind_ty(v, t),
        (Ty::Func(p1, r1), Ty::Func(p2, r2)) => {
            if p1.len() != p2.len() {
                return Err(error::TypeError::ArityMismatch {
                    expected: p2.len(),
                    got: p1.len(),
                });
            }
            for (index, (a, b)) in p1.into_iter().zip(p2).enumerate() {
                if a.capability != b.capability {
                    return Err(error::TypeError::MutableFunctionCapabilityMismatch);
                }
                unify(s, a.ty, b.ty).map_err(|err| {
                    err.with_mismatch_context(TypeMismatchContext::FunctionParam(index))
                })?;
            }
            if r1.capability != r2.capability {
                return Err(error::TypeError::MutableFunctionCapabilityMismatch);
            }
            unify(s, *r1.ty, *r2.ty)
                .map_err(|err| err.with_mismatch_context(TypeMismatchContext::FunctionReturn))
        }
        (Ty::Tuple(t1s), Ty::Tuple(t2s)) => {
            if t1s.len() != t2s.len() {
                return Err(error::TypeError::Mismatch {
                    expected: Ty::Tuple(t2s),
                    got: Ty::Tuple(t1s),
                });
            }
            for (index, (a, b)) in t1s.into_iter().zip(t2s).enumerate() {
                unify(s, a, b).map_err(|err| {
                    err.with_mismatch_context(TypeMismatchContext::TupleElement(index))
                })?;
            }
            Ok(())
        }
        (Ty::App(c1, a1), Ty::App(c2, a2)) => {
            unify(s, (*c1).clone(), (*c2).clone())?;
            if a1.len() != a2.len() {
                return Err(error::TypeError::Mismatch {
                    expected: Ty::App(c2, a2),
                    got: Ty::App(c1, a1),
                });
            }
            for (index, (v1, v2)) in a1.into_iter().zip(a2).enumerate() {
                unify(s, v1, v2).map_err(|err| {
                    err.with_mismatch_context(TypeMismatchContext::TypeArgument(index))
                })?;
            }
            Ok(())
        }
        (Ty::Record(r1), Ty::Record(r2)) => unify_rows(s, r1, r2),
        (t1, t2) => Err(error::TypeError::Mismatch {
            expected: t2,
            got: t1,
        }),
    }
}

fn unify_rows(s: &mut Subst, r1: Row, r2: Row) -> Result<(), error::TypeError> {
    debug_assert!(
        record_fields_sorted(&r1.fields),
        "left record fields must be sorted before row unification"
    );
    debug_assert!(
        record_fields_sorted(&r2.fields),
        "right record fields must be sorted before row unification"
    );
    let fields1 = r1.fields;
    let fields2 = r2.fields;

    let mut i = 0;
    let mut j = 0;
    let mut common = Vec::new();
    let mut extras1 = Vec::new();
    let mut extras2 = Vec::new();

    while i < fields1.len() && j < fields2.len() {
        match fields1[i].0.cmp(&fields2[j].0) {
            std::cmp::Ordering::Equal => {
                common.push((
                    fields1[i].0.clone(),
                    fields1[i].1.clone(),
                    fields2[j].1.clone(),
                ));
                i += 1;
                j += 1;
            }
            std::cmp::Ordering::Less => {
                extras1.push(fields1[i].clone());
                i += 1;
            }
            std::cmp::Ordering::Greater => {
                extras2.push(fields2[j].clone());
                j += 1;
            }
        }
    }
    extras1.extend_from_slice(&fields1[i..]);
    extras2.extend_from_slice(&fields2[j..]);

    for (field, t1, t2) in common {
        unify(s, t1, t2).map_err(|err| {
            err.with_mismatch_context(TypeMismatchContext::RecordField(field.clone()))
        })?;
    }

    let tail1 = s.apply(&r1.tail);
    let tail2 = s.apply(&r2.tail);

    match (tail1, tail2) {
        (Ty::Unit, Ty::Unit) => {
            if extras1.is_empty() && extras2.is_empty() {
                Ok(())
            } else {
                // Build record types that show the extra fields for a clear error.
                let left = Ty::Record(Row {
                    fields: extras1,
                    tail: Box::new(Ty::Unit),
                });
                let right = Ty::Record(Row {
                    fields: extras2,
                    tail: Box::new(Ty::Unit),
                });
                Err(error::TypeError::Mismatch {
                    expected: right,
                    got: left,
                })
            }
        }
        (Ty::Var(v), Ty::Unit) => {
            if !extras1.is_empty() {
                let extra = Ty::Record(Row {
                    fields: extras1,
                    tail: Box::new(Ty::Unit),
                });
                return Err(error::TypeError::Mismatch {
                    expected: Ty::Unit,
                    got: extra,
                });
            }
            s.bind_ty(
                v,
                Ty::Record(Row {
                    fields: extras2,
                    tail: Box::new(Ty::Unit),
                }),
            )
        }
        (Ty::Unit, Ty::Var(v)) => {
            if !extras2.is_empty() {
                let extra = Ty::Record(Row {
                    fields: extras2,
                    tail: Box::new(Ty::Unit),
                });
                return Err(error::TypeError::Mismatch {
                    expected: extra,
                    got: Ty::Unit,
                });
            }
            s.bind_ty(
                v,
                Ty::Record(Row {
                    fields: extras1,
                    tail: Box::new(Ty::Unit),
                }),
            )
        }
        (Ty::Var(v1), Ty::Var(v2)) => {
            if v1 == v2 {
                if extras1.is_empty() && extras2.is_empty() {
                    Ok(())
                } else {
                    Err(error::TypeError::OccursCheck(v1))
                }
            } else {
                let new_tail = s.fresh_var();
                s.bind_ty(
                    v1,
                    Ty::Record(Row {
                        fields: extras2,
                        tail: Box::new(new_tail.clone()),
                    }),
                )?;
                s.bind_ty(
                    v2,
                    Ty::Record(Row {
                        fields: extras1,
                        tail: Box::new(new_tail),
                    }),
                )
            }
        }
        (Ty::Record(row1), other) => {
            let mut new_fields = row1.fields;
            new_fields.extend(extras1);
            sort_record_fields(&mut new_fields);
            unify_rows(
                s,
                Row {
                    fields: new_fields,
                    tail: row1.tail,
                },
                Row {
                    fields: extras2,
                    tail: Box::new(other),
                },
            )
        }
        (other, Ty::Record(row2)) => {
            let mut new_fields = row2.fields;
            new_fields.extend(extras2);
            sort_record_fields(&mut new_fields);
            unify_rows(
                s,
                Row {
                    fields: extras1,
                    tail: Box::new(other),
                },
                Row {
                    fields: new_fields,
                    tail: row2.tail,
                },
            )
        }
        (t1, t2) => Err(error::TypeError::Mismatch {
            expected: t2,
            got: t1,
        }),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn scheme_display_uses_unicode_forall_and_letter_names() {
        // ∀ 'a. fn('a) -> 'a
        let scheme = Scheme {
            vars: vec![7],
            constraints: vec![],
            ty: Ty::Func(
                value_func_params(vec![Ty::Var(7)]),
                value_func_return(Ty::Var(7)),
            ),
        };
        assert_eq!(scheme.to_string(), "∀ 'a. fn('a) -> 'a");
    }

    #[test]
    fn scheme_display_includes_constraints_with_letter_names() {
        // ∀ 'a ['a: Iterable]. fn('a(float)) -> float
        let scheme = Scheme {
            vars: vec![90],
            constraints: vec![TraitConstraint {
                var: 90,
                trait_name: "Iterable".to_string(),
                args: vec![Ty::Var(90)],
                determinant_indexes: vec![0],
            }],
            ty: Ty::Func(
                value_func_params(vec![Ty::App(Box::new(Ty::Var(90)), vec![Ty::Float])]),
                value_func_return(Ty::Float),
            ),
        };
        assert_eq!(
            scheme.to_string(),
            "∀ 'a ['a: Iterable]. fn('a(float)) -> float"
        );
    }

    #[test]
    fn scheme_display_includes_multi_parameter_constraint_args() {
        let scheme = Scheme {
            vars: vec![1, 2],
            constraints: vec![TraitConstraint::predicate(
                "Index",
                vec![Ty::Var(1), Ty::Int, Ty::Var(2)],
                2,
                vec![0, 1],
            )],
            ty: Ty::Var(2),
        };

        assert_eq!(scheme.to_string(), "∀ 'a 'b [Index['a, int -> 'b]]. 'b");
    }

    #[test]
    fn qualified_type_display_includes_multi_parameter_constraint_args() {
        let mut names = HashMap::new();
        names.insert(1, "a".to_string());
        names.insert(2, "b".to_string());
        let ty = Ty::Qualified(
            vec![TraitConstraint::predicate(
                "Lookup",
                vec![Ty::Var(1), Ty::Con("Key".to_string()), Ty::Var(2)],
                2,
                vec![0, 1],
            )],
            Box::new(Ty::Var(2)),
        );

        assert_eq!(
            DisplayTy(&ty, &names).to_string(),
            "[Lookup['a, Key -> 'b]] 'b"
        );
    }

    #[test]
    fn scheme_display_multiple_vars_get_sequential_letters() {
        // ∀ 'a 'b. fn('a, 'b) -> 'b
        let scheme = Scheme {
            vars: vec![3, 5],
            constraints: vec![],
            ty: Ty::Func(
                value_func_params(vec![Ty::Var(3), Ty::Var(5)]),
                value_func_return(Ty::Var(5)),
            ),
        };
        assert_eq!(scheme.to_string(), "∀ 'a 'b. fn('a, 'b) -> 'b");
    }

    #[test]
    fn scheme_display_mono_type_no_forall() {
        let scheme = Scheme::mono(Ty::Float);
        assert_eq!(scheme.to_string(), "float");
    }

    #[test]
    fn tyvar_name_branches() {
        assert_eq!(type_var_name(0), "a");
        assert_eq!(type_var_name(25), "z");
        assert_eq!(type_var_name(26), "aa");
        assert_eq!(type_var_name(27), "ab");
        assert_eq!(type_var_name(51), "az");
        assert_eq!(type_var_name(52), "ba");
        assert_eq!(type_var_name(701), "zz");
        // Three-letter
        assert_eq!(type_var_name(702), "aaa");
    }

    #[test]
    fn free_type_vars_follow_display_order() {
        let ty = Ty::Func(
            value_func_params(vec![Ty::Var(78), Ty::Tuple(vec![Ty::Var(12), Ty::Var(78)])]),
            value_func_return(Ty::Var(12)),
        );

        assert_eq!(free_type_vars_in_display_order(&ty), vec![78, 12]);
    }

    #[test]
    fn scheme_display_qualified_ty_uses_pretty_names() {
        // ∀ 'a. ['a: Add] 'a — a Qualified inner type
        let scheme = Scheme {
            vars: vec![1],
            constraints: vec![],
            ty: Ty::Qualified(
                vec![TraitConstraint {
                    var: 1,
                    trait_name: "Add".to_string(),
                    args: vec![Ty::Var(1)],
                    determinant_indexes: vec![0],
                }],
                Box::new(Ty::Var(1)),
            ),
        };
        assert_eq!(scheme.to_string(), "∀ 'a. ['a: Add] 'a");
    }

    #[test]
    fn scheme_display_record_with_var_tail() {
        // ∀ 'a. #{ x: float, ..'a }
        let scheme = Scheme {
            vars: vec![2],
            constraints: vec![],
            ty: Ty::Record(Row {
                fields: vec![("x".to_string(), Ty::Float)],
                tail: Box::new(Ty::Var(2)),
            }),
        };
        assert_eq!(scheme.to_string(), "∀ 'a. #{ x: float, ..'a }");
    }

    #[test]
    fn scheme_display_constraint_with_free_var_falls_back_to_numeric() {
        // Constraint refers to var 99, not in vars → falls back to numeric
        let scheme = Scheme {
            vars: vec![0],
            constraints: vec![TraitConstraint {
                var: 99,
                trait_name: "Debug".to_string(),
                args: vec![Ty::Var(99)],
                determinant_indexes: vec![0],
            }],
            ty: Ty::Var(0),
        };
        assert_eq!(scheme.to_string(), "∀ 'a ['99: Debug]. 'a");
    }

    #[test]
    fn subst_snapshot_restore_keeps_fresh_var_counter_advancing() {
        let mut subst = Subst::new();
        assert_eq!(subst.fresh_tyvar(), 0);

        let snapshot = subst.snapshot_map();
        assert_eq!(subst.fresh_tyvar(), 1);

        subst.restore_map(snapshot);
        assert_eq!(subst.fresh_tyvar(), 2);
    }

    #[test]
    fn fresh_type_vars_record_levels() {
        let mut subst = Subst::new();

        let root = subst.fresh_tyvar();
        let nested = subst.fresh_tyvar_at(3);

        assert_eq!(subst.level_of(root), ROOT_LEVEL);
        assert_eq!(subst.level_of(nested), 3);
    }

    #[test]
    fn bind_ty_lowers_inner_var_to_outer_level() {
        let mut subst = Subst::new();
        let outer = subst.fresh_tyvar_at(0);
        let inner = subst.fresh_tyvar_at(2);

        subst
            .bind_ty(inner, Ty::Var(outer))
            .expect("binding should succeed");

        assert_eq!(subst.level_of(inner), 0);
        assert_eq!(subst.level_of(outer), 0);
    }

    #[test]
    fn bind_ty_lowers_nested_vars_in_type() {
        let mut subst = Subst::new();
        let outer = subst.fresh_tyvar_at(0);
        let inner_field = subst.fresh_tyvar_at(3);
        let inner_tail = subst.fresh_tyvar_at(4);

        subst
            .bind_ty(
                outer,
                Ty::Record(Row {
                    fields: vec![("x".to_string(), Ty::Var(inner_field))],
                    tail: Box::new(Ty::Var(inner_tail)),
                }),
            )
            .expect("binding should succeed");

        assert_eq!(subst.level_of(outer), 0);
        assert_eq!(subst.level_of(inner_field), 0);
        assert_eq!(subst.level_of(inner_tail), 0);
    }

    #[test]
    fn checkpoint_restore_rolls_back_level_lowering() {
        let mut subst = Subst::new();
        let outer = subst.fresh_tyvar_at(0);
        let inner = subst.fresh_tyvar_at(2);
        let checkpoint = subst.checkpoint();

        subst
            .bind_ty(outer, Ty::Tuple(vec![Ty::Var(inner)]))
            .expect("binding should succeed");
        assert_eq!(subst.level_of(inner), 0);

        subst.restore_checkpoint(checkpoint);

        assert_eq!(subst.apply(&Ty::Var(outer)), Ty::Var(outer));
        assert_eq!(subst.level_of(inner), 2);
    }

    #[test]
    fn subst_checkpoint_restore_rolls_back_bindings_but_not_fresh_var_counter() {
        let mut subst = Subst::new();
        assert_eq!(subst.fresh_tyvar(), 0);

        let checkpoint = subst.checkpoint();
        subst.bind_ty(0, Ty::Float).expect("binding should succeed");
        assert_eq!(subst.fresh_tyvar(), 1);

        subst.restore_checkpoint(checkpoint);

        assert_eq!(subst.apply(&Ty::Var(0)), Ty::Var(0));
        assert_eq!(subst.fresh_tyvar(), 2);
    }

    #[test]
    fn subst_checkpoint_restore_preserves_previous_binding() {
        let mut subst = Subst::new();
        subst.bind_ty(0, Ty::Float).expect("binding should succeed");

        let checkpoint = subst.checkpoint();
        subst.bind_ty(0, Ty::Int).expect("rebinding should succeed");
        subst.restore_checkpoint(checkpoint);

        assert_eq!(subst.apply(&Ty::Var(0)), Ty::Float);
    }

    #[test]
    fn subst_checkpoint_discard_keeps_successful_bindings() {
        let mut subst = Subst::new();

        let checkpoint = subst.checkpoint();
        subst.bind_ty(0, Ty::Float).expect("binding should succeed");
        subst.discard_outermost_checkpoint(checkpoint);

        assert_eq!(subst.apply(&Ty::Var(0)), Ty::Float);
        let later = subst.checkpoint();
        subst.bind_ty(1, Ty::Int).expect("binding should succeed");
        subst.restore_checkpoint(later);
        assert_eq!(subst.apply(&Ty::Var(0)), Ty::Float);
        assert_eq!(subst.apply(&Ty::Var(1)), Ty::Var(1));
    }

    #[test]
    fn subst_would_change_tracks_substituted_vars_and_record_normalization() {
        let mut subst = Subst::new();
        assert!(!subst.would_change(&Ty::Func(
            value_func_params(vec![Ty::Int]),
            value_func_return(Ty::Float),
        )));

        subst.bind_ty(0, Ty::Float).expect("binding should succeed");
        assert!(subst.would_change(&Ty::Tuple(vec![Ty::Int, Ty::Var(0)])));
        assert!(!subst.would_change(&Ty::Tuple(vec![Ty::Int, Ty::Var(1)])));

        assert!(subst.would_change(&Ty::Record(Row {
            fields: vec![("b".to_string(), Ty::Int), ("a".to_string(), Ty::Float)],
            tail: Box::new(Ty::Unit),
        })));
        assert!(subst.would_change(&Ty::Record(Row {
            fields: vec![("a".to_string(), Ty::Float)],
            tail: Box::new(Ty::Record(Row {
                fields: vec![("b".to_string(), Ty::Int)],
                tail: Box::new(Ty::Unit),
            })),
        })));
    }

    #[test]
    fn env_free_vars_accumulates_through_substitution_without_quantified_vars() {
        let mut env = TypeEnv::new();
        env.insert(
            "value".to_string(),
            EnvInfo::immutable(Scheme {
                vars: vec![0],
                constraints: vec![TraitConstraint::unary(0, "Show".to_string())],
                ty: Ty::Tuple(vec![Ty::Var(0), Ty::Var(1)]),
            }),
        );

        let mut subst = Subst::new();
        subst
            .bind_ty(0, Ty::Var(99))
            .expect("quantified binding should not leak");
        subst
            .bind_ty(1, Ty::Tuple(vec![Ty::Var(2), Ty::Int]))
            .expect("free binding should resolve");

        assert_eq!(env.free_vars(&subst), HashSet::from([2]));
    }

    #[test]
    fn env_free_vars_include_nested_qualified_constraint_args() {
        let mut env = TypeEnv::new();
        env.insert(
            "value".to_string(),
            EnvInfo::immutable(Scheme {
                vars: vec![0],
                constraints: vec![],
                ty: Ty::Qualified(
                    vec![TraitConstraint::predicate(
                        "Index",
                        vec![Ty::Var(0), Ty::Var(1), Ty::Var(2)],
                        2,
                        vec![0, 1],
                    )],
                    Box::new(Ty::Var(3)),
                ),
            }),
        );

        let subst = Subst::new();

        assert_eq!(env.free_vars(&subst), HashSet::from([1, 2, 3]));
    }

    #[test]
    fn free_type_vars_include_multi_param_constraint_args() {
        let ty = Ty::Qualified(
            vec![TraitConstraint::predicate(
                "Index",
                vec![Ty::Var(1), Ty::Var(2), Ty::Var(3)],
                3,
                vec![0, 1],
            )],
            Box::new(Ty::Var(4)),
        );

        assert_eq!(free_type_vars(&ty), HashSet::from([1, 2, 3, 4]));
        assert_eq!(free_type_vars_in_display_order(&ty), vec![4, 3, 1, 2]);
    }

    #[test]
    fn subst_clear_map_keeps_fresh_var_counter_advancing() {
        let mut subst = Subst::new();
        assert_eq!(subst.fresh_tyvar(), 0);
        subst.bind_ty(0, Ty::Float).expect("binding should succeed");

        subst.clear_map_keep_counter();

        assert_eq!(subst.apply(&Ty::Var(0)), Ty::Var(0));
        assert_eq!(subst.fresh_tyvar(), 1);
    }

    #[test]
    fn bind_ty_rejects_recursive_function_type() {
        let mut subst = Subst::new();

        let err = subst
            .bind_ty(
                0,
                Ty::Func(
                    value_func_params(vec![Ty::Float]),
                    value_func_return(Ty::Var(0)),
                ),
            )
            .expect_err("function result refers to the bound variable");

        assert_eq!(err, error::TypeError::OccursCheck(0));
    }

    #[test]
    fn bind_ty_rejects_recursive_record_type() {
        let mut subst = Subst::new();

        let err = subst
            .bind_ty(
                0,
                Ty::Record(Row {
                    fields: vec![("next".to_string(), Ty::Var(0))],
                    tail: Box::new(Ty::Unit),
                }),
            )
            .expect_err("record field refers to the bound variable");

        assert_eq!(err, error::TypeError::OccursCheck(0));
    }

    #[test]
    fn bind_ty_reports_option_recursion_as_mismatch() {
        let mut subst = Subst::new();

        let option_self = Ty::App(Box::new(Ty::Con("Option".to_string())), vec![Ty::Var(0)]);
        let err = subst
            .bind_ty(0, option_self.clone())
            .expect_err("option recursion should be rejected");

        assert_eq!(
            err,
            error::TypeError::Mismatch {
                expected: option_self,
                got: Ty::Var(0),
            }
        );
    }

    #[test]
    fn apply_still_sorts_record_fields_without_substitution() {
        let subst = Subst::new();

        let applied = subst.apply(&Ty::Record(Row {
            fields: vec![("z".to_string(), Ty::Float), ("a".to_string(), Ty::Unit)],
            tail: Box::new(Ty::Unit),
        }));

        assert_eq!(
            applied,
            Ty::Record(Row {
                fields: vec![("a".to_string(), Ty::Unit), ("z".to_string(), Ty::Float)],
                tail: Box::new(Ty::Unit),
            })
        );
    }

    #[test]
    fn apply_flattens_record_tail_resolved_by_substitution() {
        let mut subst = Subst::new();
        subst.map.insert(
            0,
            Ty::Record(Row {
                fields: vec![("b".to_string(), Ty::Float)],
                tail: Box::new(Ty::Unit),
            }),
        );

        let applied = subst.apply(&Ty::Record(Row {
            fields: vec![("a".to_string(), Ty::Unit)],
            tail: Box::new(Ty::Var(0)),
        }));

        assert_eq!(
            applied,
            Ty::Record(Row {
                fields: vec![("a".to_string(), Ty::Unit), ("b".to_string(), Ty::Float)],
                tail: Box::new(Ty::Unit),
            })
        );
    }

    #[test]
    fn app_arity_mismatch_preserves_type_constructors() {
        let mut subst = Subst::new();

        let err = unify(
            &mut subst,
            Ty::App(Box::new(Ty::Con("Map".to_string())), vec![Ty::Float]),
            Ty::App(
                Box::new(Ty::Con("Map".to_string())),
                vec![Ty::Float, Ty::Con("string".to_string())],
            ),
        )
        .expect_err("different type-application arities should fail");

        assert_eq!(
            err,
            error::TypeError::Mismatch {
                expected: Ty::App(
                    Box::new(Ty::Con("Map".to_string())),
                    vec![Ty::Float, Ty::Con("string".to_string())],
                ),
                got: Ty::App(Box::new(Ty::Con("Map".to_string())), vec![Ty::Float]),
            }
        );
    }

    #[test]
    fn structural_mismatches_report_second_type_as_expected() {
        let mut subst = Subst::new();
        let err = unify(
            &mut subst,
            Ty::Func(
                value_func_params(vec![Ty::Int, Ty::Float]),
                value_func_return(Ty::Unit),
            ),
            Ty::Func(
                value_func_params(vec![Ty::Int]),
                value_func_return(Ty::Unit),
            ),
        )
        .expect_err("function arity mismatch should fail");
        assert_eq!(
            err,
            error::TypeError::ArityMismatch {
                expected: 1,
                got: 2
            }
        );

        let err = unify(
            &mut subst,
            Ty::Tuple(vec![Ty::Int, Ty::Float]),
            Ty::Tuple(vec![Ty::Int]),
        )
        .expect_err("tuple arity mismatch should fail");
        assert_eq!(
            err,
            error::TypeError::Mismatch {
                expected: Ty::Tuple(vec![Ty::Int]),
                got: Ty::Tuple(vec![Ty::Int, Ty::Float]),
            }
        );

        let err = unify(
            &mut subst,
            Ty::Record(Row {
                fields: vec![("extra".to_string(), Ty::Int)],
                tail: Box::new(Ty::Unit),
            }),
            Ty::Record(Row {
                fields: vec![],
                tail: Box::new(Ty::Unit),
            }),
        )
        .expect_err("closed record extra field should fail");
        assert_eq!(
            err,
            error::TypeError::Mismatch {
                expected: Ty::Record(Row {
                    fields: vec![],
                    tail: Box::new(Ty::Unit),
                }),
                got: Ty::Record(Row {
                    fields: vec![("extra".to_string(), Ty::Int)],
                    tail: Box::new(Ty::Unit),
                }),
            }
        );
    }

    #[test]
    fn terminal_mismatch_reports_second_type_as_expected() {
        let mut subst = Subst::new();

        let err = unify(&mut subst, Ty::Int, Ty::Float).expect_err("int should not unify as float");

        assert_eq!(
            err,
            error::TypeError::Mismatch {
                expected: Ty::Float,
                got: Ty::Int,
            }
        );
        assert_eq!(
            err.to_string(),
            "type mismatch: expected `float`, got `int`"
        );
    }

    #[test]
    fn tuple_mismatch_reports_element_context() {
        let mut subst = Subst::new();

        let err = unify(
            &mut subst,
            Ty::Tuple(vec![Ty::Float, Ty::Con("bool".to_string())]),
            Ty::Tuple(vec![Ty::Float, Ty::Con("string".to_string())]),
        )
        .expect_err("tuple element mismatch should fail");

        assert_eq!(
            err,
            error::TypeError::MismatchWithContext {
                context: vec![TypeMismatchContext::TupleElement(1)],
                expected: Ty::Con("string".to_string()),
                got: Ty::Con("bool".to_string()),
            }
        );
        assert_eq!(
            err.to_string(),
            "type mismatch in tuple element 2: expected `string`, got `bool`"
        );
    }

    #[test]
    fn record_mismatch_reports_field_context() {
        let mut subst = Subst::new();

        let err = unify(
            &mut subst,
            Ty::Record(Row {
                fields: vec![("name".to_string(), Ty::Con("string".to_string()))],
                tail: Box::new(Ty::Unit),
            }),
            Ty::Record(Row {
                fields: vec![("name".to_string(), Ty::Float)],
                tail: Box::new(Ty::Unit),
            }),
        )
        .expect_err("record field mismatch should fail");

        assert_eq!(
            err,
            error::TypeError::MismatchWithContext {
                context: vec![TypeMismatchContext::RecordField("name".to_string())],
                expected: Ty::Float,
                got: Ty::Con("string".to_string()),
            }
        );
        assert_eq!(
            err.to_string(),
            "type mismatch in record field `name`: expected `float`, got `string`"
        );
    }

    #[test]
    fn nested_mismatch_reports_outer_to_inner_context() {
        let mut subst = Subst::new();

        let err = unify(
            &mut subst,
            Ty::Tuple(vec![Ty::Record(Row {
                fields: vec![("ok".to_string(), Ty::Con("bool".to_string()))],
                tail: Box::new(Ty::Unit),
            })]),
            Ty::Tuple(vec![Ty::Record(Row {
                fields: vec![("ok".to_string(), Ty::Float)],
                tail: Box::new(Ty::Unit),
            })]),
        )
        .expect_err("nested mismatch should fail");

        assert_eq!(
            err,
            error::TypeError::MismatchWithContext {
                context: vec![
                    TypeMismatchContext::TupleElement(0),
                    TypeMismatchContext::RecordField("ok".to_string()),
                ],
                expected: Ty::Float,
                got: Ty::Con("bool".to_string()),
            }
        );
        assert_eq!(
            err.to_string(),
            "type mismatch in tuple element 1, record field `ok`: expected `float`, got `bool`"
        );
    }
}
