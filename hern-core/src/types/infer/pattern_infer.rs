//! Pattern inference and binding.
//!
//! Patterns check destructuring shapes against an expected type, extend the local
//! environment with bound names, and enforce whether the binding context permits
//! mutable-place requirements.

use super::*;

pub(super) fn syntax_capture_ty(repeat: bool) -> Ty {
    let syntax = Ty::Con("Syntax".to_string());
    if repeat {
        Ty::App(Box::new(Ty::Con("Array".to_string())), vec![syntax])
    } else {
        syntax
    }
}

impl Infer {
    pub(super) fn check_pattern(
        &mut self,
        pat: &Pattern,
        scrutinee_ty: Ty,
        env: &mut TypeEnv,
        binding_mutable: bool,
    ) -> Result<(), TypeError> {
        let binding_info = |scheme| {
            if binding_mutable {
                EnvInfo::mutable_binding(scheme)
            } else {
                EnvInfo::immutable(scheme)
            }
        };
        match pat {
            Pattern::Wildcard => Ok(()),
            Pattern::StringLit(_) => {
                unify(&mut self.subst, scrutinee_ty, Ty::Con("string".to_string()))
            }
            Pattern::NumberLit(NumberLiteral::Int(_)) | Pattern::IntRange { .. } => {
                unify(&mut self.subst, scrutinee_ty, Ty::Int)
            }
            Pattern::NumberLit(NumberLiteral::Float(_)) => {
                unify(&mut self.subst, scrutinee_ty, Ty::Float)
            }
            Pattern::BoolLit(_) => {
                unify(&mut self.subst, scrutinee_ty, Ty::Con("bool".to_string()))
            }
            Pattern::SyntaxQuote(pattern) => {
                unify(&mut self.subst, scrutinee_ty, Ty::Con("Syntax".to_string()))?;
                let mut captures = Vec::new();
                crate::syntax::collect_syntax_pattern_captures(pattern, &mut captures);
                for capture in captures {
                    let capture_info = SyntaxCaptureInfo {
                        name: capture.name.clone(),
                        category: capture.category,
                        repeat: capture.repeat,
                        span: capture.span,
                    };
                    self.metadata
                        .record_binding_type(capture.span, syntax_capture_ty(capture.repeat));
                    self.metadata.record_syntax_capture(capture_info.clone());
                    env.insert(
                        capture.name,
                        binding_info(Scheme::mono(syntax_capture_ty(capture.repeat)))
                            .with_syntax_capture(capture_info),
                    );
                }
                Ok(())
            }
            Pattern::Variable(name, span) => {
                self.metadata
                    .record_binding_type(*span, scrutinee_ty.clone());
                env.insert(name.clone(), binding_info(Scheme::mono(scrutinee_ty)));
                Ok(())
            }
            Pattern::Constructor { name, binding } => {
                let info = self
                    .types
                    .variant_env
                    .0
                    .get(name)
                    .ok_or_else(|| {
                        pattern_unknown_constructor_error(name, &self.subst.apply(&scrutinee_ty))
                    })?
                    .clone();

                let mut param_map: HashMap<String, TyVar> = HashMap::new();
                let type_args: Vec<Ty> = info
                    .type_params
                    .iter()
                    .map(|p| {
                        let v = self.fresh_var();
                        param_map.insert(p.clone(), v);
                        Ty::Var(v)
                    })
                    .collect();

                let con_ty = if type_args.is_empty() {
                    Ty::Con(info.type_name.clone())
                } else {
                    Ty::App(Box::new(Ty::Con(info.type_name.clone())), type_args)
                };
                unify(&mut self.subst, scrutinee_ty, con_ty)?;

                if let Some(binding) = binding {
                    let payload_ty = match &info.payload {
                        Some(ast_ty) => self.ast_to_ty_with_vars(ast_ty, &mut param_map)?,
                        None => {
                            return Err(TypeError::UnboundVariable(format!(
                                "variant `{}` has no payload to bind",
                                name
                            )));
                        }
                    };
                    self.check_pattern(binding, payload_ty, env, binding_mutable)?;
                }
                Ok(())
            }
            Pattern::Record { fields, rest } => {
                let tail_var = self.fresh_var();
                let tail = if rest.is_some() {
                    Ty::Var(tail_var)
                } else {
                    Ty::Unit
                };

                // Build sorted field-type pairs for unification.
                let mut field_tys: Vec<(String, Ty)> = fields
                    .iter()
                    .map(|(field_name, _, _)| (field_name.clone(), self.fresh_ty()))
                    .collect();
                field_tys.sort_by(|(a, _), (b, _)| a.cmp(b));

                unify(
                    &mut self.subst,
                    scrutinee_ty,
                    Ty::Record(Row {
                        fields: field_tys.clone(),
                        tail: Box::new(tail),
                    }),
                )?;

                // Bind each field's type to its binding name by looking up the field name
                // in the (sorted) field_tys rather than relying on positional zip.
                for (field_name, binding_name, binding_span) in fields.iter() {
                    if binding_name == "_" {
                        continue;
                    }
                    if let Some((_, field_ty)) = field_tys.iter().find(|(n, _)| n == field_name) {
                        self.metadata
                            .record_binding_type(*binding_span, self.subst.apply(field_ty));
                        env.insert(
                            binding_name.clone(),
                            binding_info(Scheme::mono(self.subst.apply(field_ty))),
                        );
                    }
                }

                if let Some(Some((rest_name, rest_span))) = rest {
                    let rest_ty = self.subst.apply(&Ty::Var(tail_var));
                    self.metadata
                        .record_binding_type(*rest_span, rest_ty.clone());
                    env.insert(rest_name.clone(), binding_info(Scheme::mono(rest_ty)));
                }
                Ok(())
            }
            Pattern::List { elements, rest } => {
                let elt_ty = self.fresh_ty();
                let arr_ty = Ty::App(Box::new(Ty::Con("Array".to_string())), vec![elt_ty.clone()]);
                unify(&mut self.subst, scrutinee_ty, arr_ty.clone())?;

                for elem in elements {
                    self.check_pattern(elem, elt_ty.clone(), env, binding_mutable)?;
                }
                if let Some(Some((rest_name, rest_span))) = rest {
                    self.metadata
                        .record_binding_type(*rest_span, arr_ty.clone());
                    env.insert(rest_name.clone(), binding_info(Scheme::mono(arr_ty)));
                }
                Ok(())
            }
            Pattern::Tuple(pats) => {
                let elem_tys: Vec<Ty> = pats.iter().map(|_| self.fresh_ty()).collect();
                unify(&mut self.subst, scrutinee_ty, Ty::Tuple(elem_tys.clone()))?;
                for (p, t) in pats.iter().zip(elem_tys.iter()) {
                    let resolved = self.subst.apply(t);
                    self.check_pattern(p, resolved, env, binding_mutable)?;
                }
                Ok(())
            }
        }
    }

    pub(super) fn check_param_pattern(
        &mut self,
        pat: &Pattern,
        scrutinee_ty: Ty,
        env: &mut TypeEnv,
        mut_place: bool,
    ) -> Result<(), TypeError> {
        if !mut_place {
            return self.check_pattern(pat, scrutinee_ty, env, false);
        }
        let Pattern::Variable(name, span) = pat else {
            return Err(TypeError::MutableParamMustBindName);
        };
        self.metadata
            .record_binding_type(*span, scrutinee_ty.clone());
        self.metadata.record_binding_capability(
            *span,
            BindingCapabilities {
                place_mutable: true,
            },
        );
        env.insert(
            name.clone(),
            EnvInfo::immutable(Scheme::mono(scrutinee_ty)).with_place_mutable(true),
        );
        Ok(())
    }

    pub(super) fn check_exhaustive(
        &self,
        arms: &[(Pattern, Expr)],
        scrutinee_ty: &Ty,
    ) -> Result<(), TypeError> {
        let patterns: Vec<&Pattern> = arms.iter().map(|(p, _)| p).collect();
        check_exhaustive_match(&patterns, scrutinee_ty, &self.types.variant_env)
    }
}
