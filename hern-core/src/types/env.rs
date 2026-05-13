use crate::ast::{Stmt, Type};
use crate::types::{EnvInfo, Subst, Ty, TyVar, perf};
use im_rc::HashMap as ImHashMap;
use std::collections::{HashMap, HashSet};
use std::fmt;

impl fmt::Display for EnvInfo {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let prefix = if self.place_mutable {
            "mut place "
        } else if self.binding_mutable {
            "mut "
        } else {
            ""
        };
        write!(f, "{}{}", prefix, self.scheme)
    }
}

#[derive(Debug, Clone, Default)]
pub struct TypeEnv(pub ImHashMap<String, EnvInfo>);

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

    pub(super) fn free_vars(&self, s: &Subst) -> HashSet<TyVar> {
        perf::type_env_free_vars(self.0.len());
        let mut vars = HashSet::new();
        for info in self.0.values() {
            scheme_free_vars_after_apply_into(&info.scheme, s, &mut vars);
        }
        vars
    }

    #[cfg(test)]
    pub(super) fn free_vars_syntactic(&self) -> HashSet<TyVar> {
        let mut vars = HashSet::new();
        for info in self.0.values() {
            vars.extend(scheme_free_vars(&info.scheme));
        }
        vars
    }

    pub(super) fn apply_subst(&mut self, subst: &Subst) {
        perf::type_env_apply_subst(self.0.len());
        let mut updated = None;
        let mut changed = 0;
        for (name, info) in self.0.iter() {
            // Only normalize the monotype cached in the environment. Scheme
            // constraints keep referring to their scheme variables; constraint
            // substitution happens when a scheme is instantiated.
            if !subst.would_change(&info.scheme.ty) {
                continue;
            }
            let ty = subst.apply(&info.scheme.ty);
            let mut info = info.clone();
            info.scheme.ty = ty;
            updated
                .get_or_insert_with(|| self.0.clone())
                .insert(name.clone(), info);
            changed += 1;
        }
        perf::type_env_apply_subst_changed(changed);
        if let Some(updated) = updated {
            self.0 = updated;
        }
    }
}

#[cfg(test)]
fn scheme_free_vars(scheme: &crate::types::Scheme) -> HashSet<TyVar> {
    let mut vars = HashSet::new();
    crate::types::free_type_vars_into(&scheme.ty, &mut vars);
    for constraint in &scheme.constraints {
        vars.insert(constraint.var);
        for arg in &constraint.args {
            crate::types::free_type_vars_into(arg, &mut vars);
        }
    }
    for quantified in &scheme.vars {
        vars.remove(quantified);
    }
    vars
}

fn scheme_free_vars_after_apply_into(
    scheme: &crate::types::Scheme,
    subst: &Subst,
    vars: &mut HashSet<TyVar>,
) {
    collect_scheme_ty_free_vars_after_apply(&scheme.ty, &scheme.vars, subst, vars);
    for constraint in &scheme.constraints {
        if !scheme.vars.contains(&constraint.var) {
            subst.free_vars_after_apply_into(&Ty::Var(constraint.var), vars);
        }
        for arg in &constraint.args {
            collect_scheme_ty_free_vars_after_apply(arg, &scheme.vars, subst, vars);
        }
    }
}

fn collect_scheme_ty_free_vars_after_apply(
    ty: &Ty,
    quantified: &[TyVar],
    subst: &Subst,
    vars: &mut HashSet<TyVar>,
) {
    match ty {
        Ty::Var(var) => {
            if !quantified.contains(var) {
                subst.free_vars_after_apply_into(ty, vars);
            }
        }
        Ty::Qualified(constraints, ty) => {
            collect_scheme_ty_free_vars_after_apply(ty, quantified, subst, vars);
            for constraint in constraints {
                if !quantified.contains(&constraint.var) {
                    subst.free_vars_after_apply_into(&Ty::Var(constraint.var), vars);
                }
                for arg in &constraint.args {
                    collect_scheme_ty_free_vars_after_apply(arg, quantified, subst, vars);
                }
            }
        }
        Ty::Func(params, ret) => {
            for param in params {
                collect_scheme_ty_free_vars_after_apply(&param.ty, quantified, subst, vars);
            }
            collect_scheme_ty_free_vars_after_apply(&ret.ty, quantified, subst, vars);
        }
        Ty::Tuple(tys) => {
            for ty in tys {
                collect_scheme_ty_free_vars_after_apply(ty, quantified, subst, vars);
            }
        }
        Ty::App(con, args) => {
            collect_scheme_ty_free_vars_after_apply(con, quantified, subst, vars);
            for arg in args {
                collect_scheme_ty_free_vars_after_apply(arg, quantified, subst, vars);
            }
        }
        Ty::Record(row) => {
            for (_, ty) in &row.fields {
                collect_scheme_ty_free_vars_after_apply(ty, quantified, subst, vars);
            }
            collect_scheme_ty_free_vars_after_apply(&row.tail, quantified, subst, vars);
        }
        Ty::Int | Ty::Float | Ty::Unit | Ty::Never | Ty::Con(_) => {}
    }
}

impl fmt::Display for TypeEnv {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut keys: Vec<_> = self.0.keys().collect();
        keys.sort();
        for key in keys {
            writeln!(f, "  {}: {}", key, self.0.get(key).unwrap())?;
        }
        Ok(())
    }
}

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

pub(super) fn build_variant_env_from_stmts(seed_stmts: &[Stmt], stmts: &[Stmt]) -> VariantEnv {
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
