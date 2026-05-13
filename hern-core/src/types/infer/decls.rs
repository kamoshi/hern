use super::*;

impl Infer {
    pub(super) fn register_type_declarations<'a>(&mut self, stmts: impl Iterator<Item = &'a Stmt>) {
        for stmt in stmts {
            match stmt {
                Stmt::Type(td) => {
                    self.declared_types.insert(td.name.clone());
                }
                Stmt::TypeAlias {
                    name, params, ty, ..
                } => {
                    self.declared_types.insert(name.clone());
                    self.type_aliases
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
            self.trait_env.insert(td.name.clone(), td.clone());
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
                match self.op_trait_map.get(&method.name) {
                    Some(existing) if existing != &td.name => {
                        return Err(
                            TypeError::DuplicateOperator(method.name.clone()).at(stmt.span())
                        );
                    }
                    Some(_) => {}
                    None => {
                        self.op_trait_map
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
                self.known_impl_dicts.insert(dict_name);
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
                self.known_impl_dicts.remove(&dict_name);
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

            if let Some(info) = self.variant_env.0.get_mut(&name) {
                info.type_param_vars = type_param_vars;
                info.payload_ty = payload_ty;
            }
        }
    }

    pub(super) fn discard_failed_type_decl(&mut self, td: &TypeDef) {
        self.declared_types.remove(&td.name);
        for variant in &td.variants {
            self.variant_env.0.remove(&variant.name);
        }
    }
}

fn validate_trait_methods_have_target(td: &TraitDef) -> Result<(), SpannedTypeError> {
    for method in &td.methods {
        if method.params.is_empty() {
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
                    .any(|(_, ty)| ast_type_contains_var(ty, param))
                    || ast_type_contains_var(&method.ret_type, param)
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

fn ast_type_contains_var(ty: &Type, var_name: &str) -> bool {
    match ty {
        Type::Var(name) => name == var_name,
        Type::App(con, args) => {
            ast_type_contains_var(con, var_name)
                || args.iter().any(|arg| ast_type_contains_var(arg, var_name))
        }
        Type::Func(params, ret) => {
            params
                .iter()
                .any(|param| ast_type_contains_var(&param.ty, var_name))
                || ast_type_contains_var(&ret.ty, var_name)
        }
        Type::Tuple(items) => items
            .iter()
            .any(|item| ast_type_contains_var(item, var_name)),
        Type::Record(fields, _) => fields
            .iter()
            .any(|(_, field_ty)| ast_type_contains_var(field_ty, var_name)),
        Type::Ident(_) | Type::Unit | Type::Never | Type::Hole => false,
    }
}

fn impl_dict_name(impl_def: &ImplDef) -> Option<String> {
    trait_impl_arg_keys_from_ast(&impl_def.trait_args)
        .ok()
        .map(|arg_keys| trait_impl_dict_name_from_keys(&impl_def.trait_name, &arg_keys))
}
