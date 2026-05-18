//! Conversion from parsed type syntax to inference types.
//!
//! Parsed annotations are resolved into `Ty` values, including aliases, records,
//! higher-kinded applications, and locally bound type parameters.

use super::*;

impl Infer {
    pub(super) fn ast_to_ty_with_vars(
        &mut self,
        ast_ty: &Type,
        param_vars: &mut HashMap<String, TyVar>,
    ) -> Result<Ty, TypeError> {
        self.ast_to_ty_with_vars_inner(ast_ty, param_vars, &mut Vec::new())
    }

    pub(super) fn ast_to_ty_with_vars_inner(
        &mut self,
        ast_ty: &Type,
        param_vars: &mut HashMap<String, TyVar>,
        alias_stack: &mut Vec<String>,
    ) -> Result<Ty, TypeError> {
        Ok(match ast_ty {
            Type::Ident(name) => {
                if let Some((params, aliased_ty)) = self.types.aliases.get(name).cloned() {
                    if !params.is_empty() {
                        return Err(TypeError::TypeAliasArityMismatch {
                            name: name.clone(),
                            expected: params.len(),
                            got: 0,
                        });
                    }
                    return self.expand_type_alias(name, &aliased_ty, param_vars, alias_stack);
                }
                match name.as_str() {
                    "int" => Ty::Int,
                    "float" => Ty::Float,
                    "Unit" | "()" => Ty::Unit,
                    _ if self.types.declared.contains(name) => Ty::Con(name.clone()),
                    _ => return Err(TypeError::UnknownType(name.clone())),
                }
            }
            Type::Never => Ty::Never,
            Type::Var(name) => {
                if let Some(&v) = param_vars.get(name) {
                    Ty::Var(v)
                } else {
                    let v = self.fresh_var();
                    param_vars.insert(name.clone(), v);
                    Ty::Var(v)
                }
            }
            Type::Func(params, ret) => {
                let param_tys = params
                    .iter()
                    .map(|p| {
                        self.ast_to_ty_with_vars_inner(&p.ty, param_vars, alias_stack)
                            .map(|ty| {
                                if p.mut_place {
                                    FuncParam::mut_place(ty)
                                } else {
                                    FuncParam::value(ty)
                                }
                            })
                    })
                    .collect::<Result<_, _>>()?;
                Ty::Func(
                    param_tys,
                    if ret.mut_place {
                        FuncReturn::fresh_place(self.ast_to_ty_with_vars_inner(
                            &ret.ty,
                            param_vars,
                            alias_stack,
                        )?)
                    } else {
                        value_func_return(self.ast_to_ty_with_vars_inner(
                            &ret.ty,
                            param_vars,
                            alias_stack,
                        )?)
                    },
                )
            }
            Type::App(con, args) => {
                if let Type::Ident(name) = &**con
                    && let Some((params, aliased_ty)) = self.types.aliases.get(name).cloned()
                {
                    if params.len() != args.len() {
                        return Err(TypeError::TypeAliasArityMismatch {
                            name: name.clone(),
                            expected: params.len(),
                            got: args.len(),
                        });
                    }
                    let mut substituted = aliased_ty;
                    for (param, arg) in params.iter().zip(args.iter()) {
                        substituted = subst_hkt_param(&substituted, param, arg);
                    }
                    return self.expand_type_alias(name, &substituted, param_vars, alias_stack);
                }
                let con_ty = self.ast_to_ty_with_vars_inner(con, param_vars, alias_stack)?;
                let arg_tys = args
                    .iter()
                    .map(|a| self.ast_to_ty_with_vars_inner(a, param_vars, alias_stack))
                    .collect::<Result<_, _>>()?;
                Ty::App(Box::new(con_ty), arg_tys)
            }
            Type::Tuple(tys) => Ty::Tuple(
                tys.iter()
                    .map(|t| self.ast_to_ty_with_vars_inner(t, param_vars, alias_stack))
                    .collect::<Result<_, _>>()?,
            ),
            Type::Record(fields, is_open) => {
                let mut field_tys: Vec<_> = fields
                    .iter()
                    .map(|(n, t)| {
                        self.ast_to_ty_with_vars_inner(t, param_vars, alias_stack)
                            .map(|ty| (n.clone(), ty))
                    })
                    .collect::<Result<_, _>>()?;
                field_tys.sort_by(|(a, _), (b, _)| a.cmp(b));
                let tail = if *is_open { self.fresh_ty() } else { Ty::Unit };
                Ty::Record(Row {
                    fields: field_tys,
                    tail: Box::new(tail),
                })
            }
            Type::Unit => Ty::Unit,
            Type::Hole => self.fresh_ty(),
        })
    }

    pub(super) fn expand_type_alias(
        &mut self,
        name: &str,
        aliased_ty: &Type,
        param_vars: &mut HashMap<String, TyVar>,
        alias_stack: &mut Vec<String>,
    ) -> Result<Ty, TypeError> {
        if alias_stack.iter().any(|alias| alias == name) {
            return Err(TypeError::RecursiveTypeAlias(name.to_string()));
        }

        alias_stack.push(name.to_string());
        let result = self.ast_to_ty_with_vars_inner(aliased_ty, param_vars, alias_stack);
        alias_stack.pop();
        result
    }
}
