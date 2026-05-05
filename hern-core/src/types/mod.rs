mod env;
pub mod error;
pub mod infer;
mod patterns;
mod type_syntax;
mod value;

pub use env::{TypeEnv, VariantEnv, VariantInfo};
pub use value::{is_fresh_mutable_place, is_value};

use std::collections::{HashMap, HashSet};
use std::fmt;
use std::sync::OnceLock;

pub type TyVar = u32;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct TraitConstraint {
    pub var: TyVar,
    pub trait_name: String,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Ty {
    F64,
    Unit,
    Qualified(Vec<TraitConstraint>, Box<Ty>),
    Tuple(Vec<Ty>),
    Func(Vec<Ty>, Box<Ty>),
    Var(TyVar),
    /// A concrete type constructor: `bool`, `Array`, `Option`
    Con(String),
    /// Type application: `Array[f64]`, `Map[string, i32]`
    App(Box<Ty>, Vec<Ty>),
    Record(Row),
}

#[derive(Debug, Clone, PartialEq)]
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
            Ty::F64 => write!(f, "f64"),
            Ty::Unit => write!(f, "()"),
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
                    match names.get(&c.var) {
                        Some(name) => write!(f, "'{}: {}", name, c.trait_name)?,
                        None => write!(f, "'{}: {}", c.var, c.trait_name)?,
                    }
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
                    write!(f, "{}", DisplayTy(p, names))?;
                }
                write!(f, ") -> {}", DisplayTy(ret, names))
            }
            Ty::Record(row) => {
                write!(f, "#{{ ")?;
                for (i, (name, ty)) in row.fields.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}: {}", name, DisplayTy(ty, names))?;
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

pub fn display_ty_with_var_names(ty: &Ty, names: &HashMap<TyVar, String>) -> String {
    DisplayTy(ty, names).to_string()
}

pub fn display_ty_with_var_names_and_param_capabilities(
    ty: &Ty,
    names: &HashMap<TyVar, String>,
    capabilities: &[ParamCapability],
) -> String {
    DisplayTyWithParamCapabilities {
        ty,
        names,
        capabilities,
    }
    .to_string()
}

struct DisplayTyWithParamCapabilities<'a> {
    ty: &'a Ty,
    names: &'a HashMap<TyVar, String>,
    capabilities: &'a [ParamCapability],
}

impl fmt::Display for DisplayTyWithParamCapabilities<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.ty {
            Ty::Qualified(_, inner) => write!(f, "{}", DisplayTy(inner, self.names)),
            Ty::Func(params, ret) => {
                write!(f, "fn(")?;
                for (idx, param) in params.iter().enumerate() {
                    if idx > 0 {
                        write!(f, ", ")?;
                    }
                    if self
                        .capabilities
                        .get(idx)
                        .is_some_and(|capability| capability.is_mut_place())
                    {
                        write!(f, "mut ")?;
                    }
                    write!(f, "{}", DisplayTy(param, self.names))?;
                }
                write!(f, ") -> {}", DisplayTy(ret, self.names))
            }
            ty => write!(f, "{}", DisplayTy(ty, self.names)),
        }
    }
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
                }
            }
            Ty::Tuple(items) => {
                for item in items {
                    collect(item, vars);
                }
            }
            Ty::Func(params, ret) => {
                for param in params {
                    collect(param, vars);
                }
                collect(ret, vars);
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
            Ty::F64 | Ty::Unit | Ty::Con(_) => {}
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
    pub param_capabilities: Vec<ParamCapability>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ParamCapability {
    Value,
    MutPlace,
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
                    match names.get(&c.var) {
                        Some(name) => write!(f, "'{}: {}", name, c.trait_name)?,
                        None => write!(f, "'{}: {}", c.var, c.trait_name)?,
                    }
                }
                write!(f, "]")?;
            }
            write!(f, ". {}", DisplayTy(&self.ty, &names))
        }
    }
}

impl Scheme {
    pub fn mono(ty: Ty) -> Self {
        Self {
            vars: vec![],
            constraints: vec![],
            ty,
            param_capabilities: vec![],
        }
    }

    pub fn with_param_capabilities(mut self, param_capabilities: Vec<ParamCapability>) -> Self {
        self.param_capabilities = param_capabilities;
        self
    }

    pub fn param_capability(&self, idx: usize) -> ParamCapability {
        self.param_capabilities
            .get(idx)
            .copied()
            .unwrap_or(ParamCapability::Value)
    }

    pub fn has_mut_place_params(&self) -> bool {
        self.param_capabilities.iter().any(|cap| cap.is_mut_place())
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

pub struct Subst {
    map: HashMap<TyVar, Ty>,
    next_var: TyVar,
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
            next_var: 0,
        }
    }

    /// Allocate a fresh type variable ID without wrapping it in `Ty::Var`.
    pub fn fresh_tyvar(&mut self) -> TyVar {
        let v = self.next_var;
        self.next_var += 1;
        v
    }

    /// Snapshots the unification map so a caller can roll back the substitution after a
    /// failed inference attempt while leaving the fresh-variable counter intact.
    pub fn snapshot_map(&self) -> HashMap<TyVar, Ty> {
        self.map.clone()
    }

    /// Restores a previously [`snapshot_map`]ped substitution. Does not touch `next_var`,
    /// so fresh variables allocated since the snapshot remain accounted for.
    pub fn restore_map(&mut self, map: HashMap<TyVar, Ty>) {
        self.map = map;
    }

    /// Allocate a fresh type variable wrapped as `Ty::Var`.
    pub fn fresh_var(&mut self) -> Ty {
        Ty::Var(self.fresh_tyvar())
    }

    pub fn apply(&self, ty: &Ty) -> Ty {
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
                    .filter_map(|c| match self.apply(&Ty::Var(c.var)) {
                        Ty::Var(var) => Some(TraitConstraint {
                            var,
                            trait_name: c.trait_name.clone(),
                        }),
                        _ => None,
                    })
                    .collect(),
                Box::new(self.apply(ty)),
            ),
            Ty::Func(params, ret) => Ty::Func(
                params.iter().map(|p| self.apply(p)).collect(),
                Box::new(self.apply(ret)),
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
                    fields.sort_by(|(a, _), (b, _)| a.cmp(b));
                    Ty::Record(Row {
                        fields,
                        tail: inner_row.tail,
                    })
                } else {
                    fields.sort_by(|(a, _), (b, _)| a.cmp(b));
                    Ty::Record(Row {
                        fields,
                        tail: Box::new(tail),
                    })
                }
            }
            t => t.clone(),
        }
    }

    pub fn apply_scheme(&self, scheme: &Scheme) -> Scheme {
        Scheme {
            vars: scheme.vars.clone(),
            constraints: scheme.constraints.clone(),
            ty: self.apply(&scheme.ty),
            param_capabilities: scheme.param_capabilities.clone(),
        }
    }

    pub fn bind_ty(&mut self, v: TyVar, t: Ty) -> Result<(), error::TypeError> {
        let t = self.apply(&t);
        if let Ty::Var(v2) = t
            && v == v2
        {
            return Ok(());
        }
        if free_type_vars(&t).contains(&v) {
            return Err(error::TypeError::OccursCheck(v));
        }
        self.map.insert(v, t);
        Ok(())
    }
}

pub fn free_type_vars(ty: &Ty) -> HashSet<TyVar> {
    let mut vars = HashSet::new();
    match ty {
        Ty::Var(v) => {
            vars.insert(*v);
        }
        Ty::Qualified(constraints, ty) => {
            vars.extend(free_type_vars(ty));
            for constraint in constraints {
                vars.insert(constraint.var);
            }
        }
        Ty::Func(params, ret) => {
            for p in params {
                vars.extend(free_type_vars(p));
            }
            vars.extend(free_type_vars(ret));
        }
        Ty::Tuple(tys) => {
            for t in tys {
                vars.extend(free_type_vars(t));
            }
        }
        Ty::App(con, args) => {
            vars.extend(free_type_vars(con));
            for a in args {
                vars.extend(free_type_vars(a));
            }
        }
        Ty::Record(row) => {
            for (_, t) in &row.fields {
                vars.extend(free_type_vars(t));
            }
            vars.extend(free_type_vars(&row.tail));
        }
        _ => {}
    }
    vars
}

pub fn unify(s: &mut Subst, t1: Ty, t2: Ty) -> Result<(), error::TypeError> {
    let t1 = s.apply(&t1);
    let t2 = s.apply(&t2);

    match (t1, t2) {
        (Ty::F64, Ty::F64) | (Ty::Unit, Ty::Unit) => Ok(()),
        (Ty::Con(n1), Ty::Con(n2)) if n1 == n2 => Ok(()),
        (Ty::Var(v), t) | (t, Ty::Var(v)) => s.bind_ty(v, t),
        (Ty::Qualified(_, t1), Ty::Qualified(_, t2)) => unify(s, *t1, *t2),
        (Ty::Qualified(_, t1), t2) => unify(s, *t1, t2),
        (t1, Ty::Qualified(_, t2)) => unify(s, t1, *t2),
        (Ty::Func(p1, r1), Ty::Func(p2, r2)) => {
            if p1.len() != p2.len() {
                return Err(error::TypeError::ArityMismatch {
                    expected: p1.len(),
                    got: p2.len(),
                });
            }
            for (a, b) in p1.into_iter().zip(p2.into_iter()) {
                unify(s, a, b)?;
            }
            unify(s, *r1, *r2)
        }
        (Ty::Tuple(t1s), Ty::Tuple(t2s)) => {
            if t1s.len() != t2s.len() {
                return Err(error::TypeError::Mismatch(Ty::Tuple(t1s), Ty::Tuple(t2s)));
            }
            for (a, b) in t1s.into_iter().zip(t2s.into_iter()) {
                unify(s, a, b)?;
            }
            Ok(())
        }
        (Ty::App(c1, a1), Ty::App(c2, a2)) => {
            unify(s, *c1, *c2)?;
            if a1.len() != a2.len() {
                return Err(error::TypeError::Mismatch(
                    Ty::App(Box::new(Ty::Unit), a1),
                    Ty::App(Box::new(Ty::Unit), a2),
                ));
            }
            for (v1, v2) in a1.into_iter().zip(a2.into_iter()) {
                unify(s, v1, v2)?;
            }
            Ok(())
        }
        (Ty::Record(r1), Ty::Record(r2)) => unify_rows(s, r1, r2),
        (t1, t2) => Err(error::TypeError::Mismatch(t2, t1)),
    }
}

fn unify_rows(s: &mut Subst, r1: Row, r2: Row) -> Result<(), error::TypeError> {
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
                common.push((fields1[i].1.clone(), fields2[j].1.clone()));
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

    for (t1, t2) in common {
        unify(s, t1, t2)?;
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
                Err(error::TypeError::Mismatch(left, right))
            }
        }
        (Ty::Var(v), Ty::Unit) => {
            if !extras1.is_empty() {
                let extra = Ty::Record(Row {
                    fields: extras1,
                    tail: Box::new(Ty::Unit),
                });
                return Err(error::TypeError::Mismatch(extra, Ty::Unit));
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
                return Err(error::TypeError::Mismatch(Ty::Unit, extra));
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
            new_fields.sort_by(|(a, _), (b, _)| a.cmp(b));
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
            new_fields.sort_by(|(a, _), (b, _)| a.cmp(b));
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
        (t1, t2) => Err(error::TypeError::Mismatch(t1, t2)),
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
            ty: Ty::Func(vec![Ty::Var(7)], Box::new(Ty::Var(7))),
            param_capabilities: vec![],
        };
        assert_eq!(scheme.to_string(), "∀ 'a. fn('a) -> 'a");
    }

    #[test]
    fn scheme_display_includes_constraints_with_letter_names() {
        // ∀ 'a ['a: Iterable]. fn('a(f64)) -> f64
        let scheme = Scheme {
            vars: vec![90],
            constraints: vec![TraitConstraint {
                var: 90,
                trait_name: "Iterable".to_string(),
            }],
            ty: Ty::Func(
                vec![Ty::App(Box::new(Ty::Var(90)), vec![Ty::F64])],
                Box::new(Ty::F64),
            ),
            param_capabilities: vec![],
        };
        assert_eq!(
            scheme.to_string(),
            "∀ 'a ['a: Iterable]. fn('a(f64)) -> f64"
        );
    }

    #[test]
    fn scheme_display_multiple_vars_get_sequential_letters() {
        // ∀ 'a 'b. fn('a, 'b) -> 'b
        let scheme = Scheme {
            vars: vec![3, 5],
            constraints: vec![],
            ty: Ty::Func(vec![Ty::Var(3), Ty::Var(5)], Box::new(Ty::Var(5))),
            param_capabilities: vec![],
        };
        assert_eq!(scheme.to_string(), "∀ 'a 'b. fn('a, 'b) -> 'b");
    }

    #[test]
    fn scheme_display_mono_type_no_forall() {
        let scheme = Scheme::mono(Ty::F64);
        assert_eq!(scheme.to_string(), "f64");
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
            vec![Ty::Var(78), Ty::Tuple(vec![Ty::Var(12), Ty::Var(78)])],
            Box::new(Ty::Var(12)),
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
                }],
                Box::new(Ty::Var(1)),
            ),
            param_capabilities: vec![],
        };
        assert_eq!(scheme.to_string(), "∀ 'a. ['a: Add] 'a");
    }

    #[test]
    fn scheme_display_record_with_var_tail() {
        // ∀ 'a. #{ x: f64, ..'a }
        let scheme = Scheme {
            vars: vec![2],
            constraints: vec![],
            ty: Ty::Record(Row {
                fields: vec![("x".to_string(), Ty::F64)],
                tail: Box::new(Ty::Var(2)),
            }),
            param_capabilities: vec![],
        };
        assert_eq!(scheme.to_string(), "∀ 'a. #{ x: f64, ..'a }");
    }

    #[test]
    fn scheme_display_constraint_with_free_var_falls_back_to_numeric() {
        // Constraint refers to var 99, not in vars → falls back to numeric
        let scheme = Scheme {
            vars: vec![0],
            constraints: vec![TraitConstraint {
                var: 99,
                trait_name: "Debug".to_string(),
            }],
            ty: Ty::Var(0),
            param_capabilities: vec![],
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
}
