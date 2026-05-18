//! Type scheme instantiation and generalization.
//!
//! This module owns the boundary between monotypes in the current inference level
//! and polymorphic schemes stored in environments, including trait constraints
//! attached to those schemes.

use super::*;

pub(super) struct InstantiatedScheme {
    pub(super) ty: Ty,
    pub(super) constraints: Vec<TraitConstraint>,
}

impl Infer {
    pub(super) fn instantiate_scheme(&mut self, scheme: &Scheme) -> InstantiatedScheme {
        let mut map = HashMap::new();
        for &v in &scheme.vars {
            map.insert(v, Ty::Var(self.fresh_var()));
        }
        // Only keep constraints whose variable was actually remapped to a fresh Var.
        // If a var somehow mapped to a concrete type, its constraint is already resolved.
        let constraints = scheme
            .constraints
            .iter()
            .filter_map(|c| match map.get(&c.var) {
                Some(Ty::Var(v)) => Some(TraitConstraint {
                    var: *v,
                    trait_name: c.trait_name.clone(),
                    args: c
                        .args
                        .iter()
                        .map(|arg| self.apply_inst(arg, &map))
                        .collect(),
                    determinant_indexes: c.determinant_indexes.clone(),
                }),
                Some(_) => None,
                None => Some(c.clone()),
            })
            .collect();
        InstantiatedScheme {
            ty: self.apply_inst(&scheme.ty, &map),
            constraints,
        }
    }

    pub(super) fn instantiate(&mut self, scheme: &Scheme) -> Ty {
        self.instantiate_scheme(scheme).ty
    }

    pub(super) fn instantiate_value(&mut self, scheme: &Scheme) -> Ty {
        let instantiated = self.instantiate_scheme(scheme);
        if instantiated.constraints.is_empty() {
            instantiated.ty
        } else {
            Ty::Qualified(instantiated.constraints, Box::new(instantiated.ty))
        }
    }

    pub(super) fn apply_inst(&self, ty: &Ty, map: &HashMap<TyVar, Ty>) -> Ty {
        match ty {
            Ty::Var(v) => map.get(v).cloned().unwrap_or(Ty::Var(*v)),
            Ty::Qualified(constraints, ty) => Ty::Qualified(
                constraints
                    .iter()
                    .filter_map(|c| match map.get(&c.var) {
                        Some(Ty::Var(var)) => Some(TraitConstraint {
                            var: *var,
                            trait_name: c.trait_name.clone(),
                            args: c.args.iter().map(|arg| self.apply_inst(arg, map)).collect(),
                            determinant_indexes: c.determinant_indexes.clone(),
                        }),
                        Some(_) => None,
                        None => Some(c.clone()),
                    })
                    .collect(),
                Box::new(self.apply_inst(ty, map)),
            ),
            Ty::Func(params, ret) => Ty::Func(
                params
                    .iter()
                    .map(|p| FuncParam {
                        ty: self.apply_inst(&p.ty, map),
                        capability: p.capability,
                    })
                    .collect(),
                FuncReturn {
                    ty: Box::new(self.apply_inst(&ret.ty, map)),
                    capability: ret.capability,
                },
            ),
            Ty::Tuple(tys) => Ty::Tuple(tys.iter().map(|t| self.apply_inst(t, map)).collect()),
            Ty::App(con, args) => Ty::App(
                Box::new(self.apply_inst(con, map)),
                args.iter().map(|a| self.apply_inst(a, map)).collect(),
            ),
            Ty::Record(row) => Ty::Record(Row {
                fields: row
                    .fields
                    .iter()
                    .map(|(n, t)| (n.clone(), self.apply_inst(t, map)))
                    .collect(),
                tail: Box::new(self.apply_inst(&row.tail, map)),
            }),
            t => t.clone(),
        }
    }
}
