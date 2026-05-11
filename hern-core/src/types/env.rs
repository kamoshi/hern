use crate::ast::{Stmt, Type};
use crate::types::{EnvInfo, Subst, Ty, TyVar, free_type_vars};
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

    pub(super) fn free_vars(&self, s: &Subst) -> HashSet<TyVar> {
        let mut vars = HashSet::new();
        for info in self.0.values() {
            for var in scheme_free_vars(&info.scheme) {
                vars.extend(free_type_vars(&s.apply(&Ty::Var(var))));
            }
        }
        vars
    }

    pub(super) fn free_vars_syntactic(&self) -> HashSet<TyVar> {
        let mut vars = HashSet::new();
        for info in self.0.values() {
            vars.extend(scheme_free_vars(&info.scheme));
        }
        vars
    }
}

fn scheme_free_vars(scheme: &crate::types::Scheme) -> HashSet<TyVar> {
    let mut vars = free_type_vars(&scheme.ty);
    for constraint in &scheme.constraints {
        vars.insert(constraint.var);
    }
    for quantified in &scheme.vars {
        vars.remove(quantified);
    }
    vars
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
