//! Inference for top-level declarations and declared type surfaces.
//!
//! Declarations establish names, schemes, variant constructors, trait
//! definitions, and inherent method entries that expression inference later
//! consumes.

use super::*;

impl Infer {
    pub(super) fn validate_type_trait_name_collisions(
        &self,
        seed_stmts: &[Stmt],
        stmts: &[Stmt],
    ) -> Result<(), SpannedTypeError> {
        let mut in_scope_type_names = self.types.declared.clone();
        let mut in_scope_trait_names: HashSet<String> = self.traits.env.keys().cloned().collect();
        for stmt in seed_stmts {
            match stmt {
                Stmt::Type(td) => {
                    in_scope_type_names.insert(td.name.clone());
                }
                Stmt::TypeAlias { name, .. } => {
                    in_scope_type_names.insert(name.clone());
                }
                Stmt::Trait(td) => {
                    in_scope_trait_names.insert(td.name.clone());
                }
                _ => {}
            }
        }

        let mut type_names: HashMap<&str, SourceSpan> = HashMap::new();
        for stmt in stmts {
            match stmt {
                Stmt::Type(td) => {
                    if in_scope_trait_names.contains(&td.name) {
                        return Err(
                            TypeError::DuplicateTypeTraitName(td.name.clone()).at(td.name_span)
                        );
                    }
                    type_names.entry(&td.name).or_insert(td.name_span);
                }
                Stmt::TypeAlias {
                    name, name_span, ..
                } => {
                    if in_scope_trait_names.contains(name) {
                        return Err(TypeError::DuplicateTypeTraitName(name.clone()).at(*name_span));
                    }
                    type_names.entry(name).or_insert(*name_span);
                }
                _ => {}
            }
        }
        for stmt in stmts {
            let Stmt::Trait(td) = stmt else {
                continue;
            };
            if in_scope_type_names.contains(&td.name) || type_names.contains_key(td.name.as_str()) {
                return Err(TypeError::DuplicateTypeTraitName(td.name.clone()).at(td.name_span));
            }
        }
        Ok(())
    }

    pub(super) fn register_type_declarations<'a>(&mut self, stmts: impl Iterator<Item = &'a Stmt>) {
        for stmt in stmts {
            match stmt {
                Stmt::Type(td) => {
                    self.types.declared.insert(td.name.clone());
                }
                Stmt::TypeAlias {
                    name, params, ty, ..
                } => {
                    self.types.declared.insert(name.clone());
                    self.types
                        .aliases
                        .insert(name.clone(), (params.clone(), ty.clone()));
                }
                _ => {}
            }
        }
        self.resolve_variant_payload_types();
    }

    pub(super) fn register_traits_and_ops<'a>(
        &mut self,
        stmts: impl Iterator<Item = &'a Stmt>,
    ) -> Result<(), SpannedTypeError> {
        for stmt in stmts {
            let Stmt::Trait(td) = stmt else {
                continue;
            };
            validate_trait_methods_have_target(td)?;
            self.traits.env.insert(td.name.clone(), td.clone());
            for method in &td.methods {
                if method.fixity.is_none() {
                    continue;
                }
                if method.params.len() != 2 {
                    return Err(TypeError::TraitMethodArityMismatch {
                        trait_name: td.name.clone(),
                        method: method.name.clone(),
                        expected: 2,
                        got: method.params.len(),
                    }
                    .at(method.span));
                }
                match self.traits.op_trait_map.get(&method.name) {
                    Some(existing) if existing != &td.name => {
                        return Err(
                            TypeError::DuplicateOperator(method.name.clone()).at(stmt.span())
                        );
                    }
                    Some(_) => {}
                    None => {
                        self.traits
                            .op_trait_map
                            .insert(method.name.clone(), td.name.clone());
                    }
                }
            }
        }
        Ok(())
    }

    pub(super) fn add_constructors_and_externs(
        &mut self,
        env: &mut TypeEnv,
        stmts: &mut [Stmt],
    ) -> Result<(), SpannedTypeError> {
        for stmt in stmts {
            let span = stmt.span();
            match stmt {
                Stmt::Type(td) => self
                    .add_constructors_to_env(env, td)
                    .map_err(|err| err.at(span))?,
                Stmt::Extern {
                    name,
                    name_span,
                    ty,
                    ..
                } => {
                    let ambient = self.current_level;
                    let t = self.with_child_level(|this| {
                        let mut param_vars = HashMap::new();
                        this.ast_to_ty_with_vars(ty, &mut param_vars)
                            .map_err(|err| err.at(span))
                    })?;
                    let scheme = self.generalize_at(env, t, ambient);
                    self.metadata
                        .record_definition_scheme(*name_span, scheme.clone());
                    env.insert(name.clone(), EnvInfo::immutable(scheme));
                }
                _ => {}
            }
        }
        Ok(())
    }

    pub(super) fn register_impl_dict_names<'a>(&mut self, stmts: impl Iterator<Item = &'a Stmt>) {
        for stmt in stmts {
            if let Stmt::Impl(impl_def) = stmt
                && let Some(dict_name) = impl_dict_name(impl_def)
            {
                self.impls.known_dicts.insert(dict_name);
            }
        }
    }

    pub(super) fn remove_program_impl_dict_names<'a>(
        &mut self,
        stmts: impl Iterator<Item = &'a Stmt>,
    ) {
        for stmt in stmts {
            if let Stmt::Impl(impl_def) = stmt
                && let Some(dict_name) = impl_dict_name(impl_def)
            {
                self.impls.known_dicts.remove(&dict_name);
            }
        }
    }

    pub(super) fn add_constructors_to_env(
        &mut self,
        env: &mut TypeEnv,
        td: &TypeDef,
    ) -> Result<(), TypeError> {
        let mut param_map: HashMap<String, TyVar> = HashMap::new();
        let mut quantified: Vec<TyVar> = Vec::new();
        let mut type_args: Vec<Ty> = Vec::new();

        for p in &td.params {
            let v = self.fresh_var();
            param_map.insert(p.clone(), v);
            quantified.push(v);
            type_args.push(Ty::Var(v));
        }

        let result_ty = if type_args.is_empty() {
            Ty::Con(td.name.clone())
        } else {
            Ty::App(Box::new(Ty::Con(td.name.clone())), type_args)
        };

        let mut entries = Vec::new();
        for variant in &td.variants {
            let ty = match &variant.payload {
                None => result_ty.clone(),
                Some(payload_ast) => {
                    let mut pm = param_map.clone();
                    let payload_ty = self.ast_to_ty_with_vars(payload_ast, &mut pm)?;
                    Ty::Func(
                        value_func_params(vec![payload_ty]),
                        value_func_return(result_ty.clone()),
                    )
                }
            };
            entries.push((
                variant.name.clone(),
                EnvInfo::immutable(Scheme {
                    vars: quantified.clone(),
                    constraints: vec![],
                    ty,
                }),
            ));
        }
        for (name, info) in entries {
            env.insert(name, info);
        }
        for variant in &td.variants {
            if let Some(info) = env.get(&variant.name) {
                self.metadata
                    .record_definition_scheme(variant.name_span, info.scheme.clone());
            }
        }
        Ok(())
    }

    fn resolve_variant_payload_types(&mut self) {
        let variants: Vec<(String, Vec<String>, Option<Type>)> = self
            .types
            .variant_env
            .0
            .iter()
            .map(|(name, info)| (name.clone(), info.type_params.clone(), info.payload.clone()))
            .collect();

        for (name, type_params, payload) in variants {
            let mut param_vars = HashMap::new();
            let type_param_vars: Vec<TyVar> = type_params
                .iter()
                .map(|param| {
                    let var = self.fresh_var();
                    param_vars.insert(param.clone(), var);
                    var
                })
                .collect();

            let payload_ty = payload
                .as_ref()
                .and_then(|ty| self.ast_to_ty_with_vars(ty, &mut param_vars).ok());

            if let Some(info) = self.types.variant_env.0.get_mut(&name) {
                info.type_param_vars = type_param_vars;
                info.payload_ty = payload_ty;
            }
        }
    }

    pub(super) fn discard_failed_type_decl(&mut self, td: &TypeDef) {
        self.types.declared.remove(&td.name);
        for variant in &td.variants {
            self.types.variant_env.0.remove(&variant.name);
        }
    }
}

fn validate_trait_methods_have_target(td: &TraitDef) -> Result<(), SpannedTypeError> {
    for method in &td.methods {
        let mentions_trait_param = td.params.iter().any(|param| {
            method
                .params
                .iter()
                .any(|(_, ty)| type_contains_var(ty, param))
                || type_contains_var(&method.ret_type, param)
        });
        if !mentions_trait_param {
            return Err(TypeError::TraitMethodMissingTarget {
                trait_name: td.name.clone(),
                method: method.name.clone(),
            }
            .at(method.span));
        }
    }
    for fundep in &td.fundeps {
        for dependent in &fundep.dependents {
            let Some(param) = td.params.get(*dependent) else {
                continue;
            };
            let reachable = td.methods.iter().any(|method| {
                method
                    .params
                    .iter()
                    .any(|(_, ty)| type_contains_var(ty, param))
                    || type_contains_var(&method.ret_type, param)
            });
            if !reachable {
                return Err(TypeError::FunctionalDependencyViolation {
                    trait_name: td.name.clone(),
                    message: format!(
                        "dependent trait parameter `{}` must appear in a method signature",
                        param
                    ),
                }
                .at(td.span));
            }
        }
    }
    Ok(())
}

fn impl_dict_name(impl_def: &ImplDef) -> Option<String> {
    trait_impl_arg_keys_from_ast(&impl_def.trait_args)
        .ok()
        .map(|arg_keys| trait_impl_dict_name_from_keys(&impl_def.trait_name, &arg_keys))
}
