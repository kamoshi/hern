//! Inference for source-level test blocks.
//!
//! Test blocks are checked like scoped program fragments: declarations and
//! expressions inside the block should type-check without leaking local bindings
//! into the surrounding module environment.

use super::*;

impl Infer {
    pub(super) fn infer_test_block_collecting(
        &mut self,
        env: &TypeEnv,
        stmts: &mut [Stmt],
    ) -> Vec<SpannedTypeError> {
        let mut test_env = env.clone();
        let mut diagnostics = Vec::new();
        let mut unavailable = CollectedNames::default();

        for stmt in stmts {
            let bound = stmt_bound_names(stmt);
            let refs = stmt_referenced_names(stmt);
            if unavailable.overlaps(&refs) {
                unavailable.extend(bound);
                continue;
            }

            let subst_checkpoint = self.subst.checkpoint();
            let snapshot = InferSnapshot::capture(self, &test_env, subst_checkpoint);
            match self.infer_stmt(&mut test_env, stmt) {
                Ok(_) => {
                    if let Err(err) = self.validate_test_stmt_shape(&test_env, stmt) {
                        let failed_metadata = snapshot.metadata_added_before_failure(self);
                        snapshot.restore(self, &mut test_env);
                        self.metadata.extend_failed_statement(failed_metadata);
                        unavailable.extend(bound);
                        diagnostics.push(err);
                    } else {
                        snapshot.discard(self);
                        unavailable.remove_all(&bound);
                    }
                }
                Err(err) => {
                    let failed_metadata = snapshot.metadata_added_before_failure(self);
                    snapshot.restore(self, &mut test_env);
                    self.metadata.extend_failed_statement(failed_metadata);
                    unavailable.extend(bound);
                    diagnostics.push(err);
                }
            }
        }

        diagnostics
    }

    pub(super) fn validate_test_stmt_shape(
        &self,
        env: &TypeEnv,
        stmt: &Stmt,
    ) -> Result<(), SpannedTypeError> {
        if let Stmt::RecBlock {
            stmts: rec_stmts, ..
        } = stmt
        {
            for rec_stmt in rec_stmts {
                self.validate_test_stmt_shape(env, rec_stmt)?;
            }
            return Ok(());
        }

        let Stmt::Fn {
            name,
            name_span,
            params,
            ..
        } = stmt
        else {
            return Ok(());
        };
        if !stmt.is_test_fn() {
            return Ok(());
        }
        if !params.is_empty() {
            return Err(TypeError::InvalidTestFunction {
                name: name.clone(),
                message: format!(
                    "expected no parameters, found {} parameter{}",
                    params.len(),
                    if params.len() == 1 { "" } else { "s" }
                ),
            }
            .at(*name_span));
        }
        let Some(info) = env.get(name) else {
            debug_assert!(
                false,
                "inferred #[test] function `{name}` should be present in the local test environment"
            );
            return Err(TypeError::UnboundVariable(name.clone()).at(*name_span));
        };
        match Self::test_function_return_ty(&info.scheme.ty) {
            Some(Ty::Unit) => Ok(()),
            Some(other) => Err(TypeError::InvalidTestFunction {
                name: name.clone(),
                message: format!("expected return type unit, found {}", other),
            }
            .at(*name_span)),
            None => Err(TypeError::InvalidTestFunction {
                name: name.clone(),
                message: format!("expected a function, found {}", info.scheme.ty),
            }
            .at(*name_span)),
        }
    }

    pub(super) fn validate_duplicate_test_function_names(
        &self,
        stmts: &[Stmt],
    ) -> Vec<SpannedTypeError> {
        let mut seen: HashMap<&str, SourceSpan> = HashMap::new();
        let mut diagnostics = Vec::new();
        for stmt in stmts {
            let Stmt::TestBlock {
                stmts: test_stmts, ..
            } = stmt
            else {
                continue;
            };
            self.validate_duplicate_test_function_names_in_stmts(
                test_stmts,
                &mut seen,
                &mut diagnostics,
            );
        }
        diagnostics
    }

    pub(super) fn validate_duplicate_test_function_names_in_stmts<'a>(
        &self,
        stmts: &'a [Stmt],
        seen: &mut HashMap<&'a str, SourceSpan>,
        diagnostics: &mut Vec<SpannedTypeError>,
    ) {
        for stmt in stmts {
            match stmt {
                Stmt::Fn {
                    name, name_span, ..
                } if stmt.is_test_fn() && seen.insert(name.as_str(), *name_span).is_some() => {
                    diagnostics.push(TypeError::DuplicateTestFunction(name.clone()).at(*name_span));
                }
                Stmt::RecBlock {
                    stmts: rec_stmts, ..
                } => {
                    self.validate_duplicate_test_function_names_in_stmts(
                        rec_stmts,
                        seen,
                        diagnostics,
                    );
                }
                _ => {}
            }
        }
    }

    pub(super) fn test_function_return_ty(ty: &Ty) -> Option<&Ty> {
        match ty {
            Ty::Qualified(_, inner) => Self::test_function_return_ty(inner),
            Ty::Func(params, ret) if params.is_empty() => Some(ret.ty.as_ref()),
            Ty::Func(_, _) => None,
            _ => None,
        }
    }
}
