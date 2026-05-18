//! Inference for aggregate and range literals.
//!
//! This module handles expression forms that construct data directly: records,
//! arrays, and the built-in range family. It enforces local element/field
//! consistency, propagates expected array element types when available, and leaves
//! broader control-flow or trait-dispatch rules to sibling modules.

use super::*;

impl Infer {
    pub(super) fn infer_range_expr(
        &mut self,
        env: &TypeEnv,
        start: Option<&mut Expr>,
        end: Option<&mut Expr>,
        inclusive: bool,
    ) -> Result<Ty, SpannedTypeError> {
        let int_ty = Ty::Int;
        match (start, end, inclusive) {
            (Some(start), Some(end), false) => {
                let start_ty = self.infer_expr(env, start)?;
                unify(&mut self.subst, start_ty, int_ty.clone()).map_err(|err| {
                    err.with_mismatch_context(TypeMismatchContext::RangeStart)
                        .at(start.span)
                })?;
                let end_ty = self.infer_expr(env, end)?;
                unify(&mut self.subst, end_ty, int_ty.clone()).map_err(|err| {
                    err.with_mismatch_context(TypeMismatchContext::RangeEnd)
                        .at(end.span)
                })?;
                Ok(range_ty("Range"))
            }
            (Some(start), Some(end), true) => {
                let start_ty = self.infer_expr(env, start)?;
                unify(&mut self.subst, start_ty, int_ty.clone()).map_err(|err| {
                    err.with_mismatch_context(TypeMismatchContext::RangeStart)
                        .at(start.span)
                })?;
                let end_ty = self.infer_expr(env, end)?;
                unify(&mut self.subst, end_ty, int_ty.clone()).map_err(|err| {
                    err.with_mismatch_context(TypeMismatchContext::RangeEnd)
                        .at(end.span)
                })?;
                Ok(range_ty("RangeInclusive"))
            }
            (Some(start), None, false) => {
                let start_ty = self.infer_expr(env, start)?;
                unify(&mut self.subst, start_ty, int_ty).map_err(|err| {
                    err.with_mismatch_context(TypeMismatchContext::RangeStart)
                        .at(start.span)
                })?;
                Ok(range_ty("RangeFrom"))
            }
            (Some(_), None, true) => {
                unreachable!("parser rejects inclusive ranges without end bounds")
            }
            (None, Some(end), false) => {
                let end_ty = self.infer_expr(env, end)?;
                unify(&mut self.subst, end_ty, int_ty).map_err(|err| {
                    err.with_mismatch_context(TypeMismatchContext::RangeEnd)
                        .at(end.span)
                })?;
                Ok(range_ty("RangeTo"))
            }
            (None, Some(end), true) => {
                let end_ty = self.infer_expr(env, end)?;
                unify(&mut self.subst, end_ty, int_ty).map_err(|err| {
                    err.with_mismatch_context(TypeMismatchContext::RangeEnd)
                        .at(end.span)
                })?;
                Ok(range_ty("RangeToInclusive"))
            }
            (None, None, false) => Ok(Ty::Con("RangeFull".to_string())),
            (None, None, true) => {
                unreachable!("parser rejects inclusive ranges without end bounds")
            }
        }
    }

    pub(super) fn infer_record_expr(
        &mut self,
        env: &TypeEnv,
        entries: &mut [RecordEntry],
        span: SourceSpan,
    ) -> Result<Ty, SpannedTypeError> {
        let mut field_tys: Vec<(String, Ty)> = Vec::new();
        let mut tail = Ty::Unit;
        for entry in entries {
            match entry {
                RecordEntry::Field(name, expr) => {
                    let ty = self.infer_expr(env, expr)?;
                    merge_record_field(&mut field_tys, name.clone(), ty);
                }
                RecordEntry::Spread(expr) => {
                    let spread_ty = self.infer_expr(env, expr)?;
                    let tail_var = self.fresh_ty();
                    unify(
                        &mut self.subst,
                        spread_ty.clone(),
                        Ty::Record(Row {
                            fields: vec![],
                            tail: Box::new(tail_var),
                        }),
                    )?;
                    let resolved_spread = self.subst.apply(&spread_ty);
                    let Ty::Record(row) = resolved_spread else {
                        return Err(TypeError::Mismatch(
                            Ty::Record(Row {
                                fields: vec![],
                                tail: Box::new(self.fresh_ty()),
                            }),
                            resolved_spread,
                        )
                        .at(span));
                    };
                    for (name, ty) in row.fields {
                        merge_record_field(&mut field_tys, name, ty);
                    }
                    tail = merge_record_spread_tail(&mut self.subst, tail, *row.tail)
                        .map_err(|err| err.at(span))?;
                }
            }
        }
        field_tys.sort_by(|(a, _), (b, _)| a.cmp(b));
        Ok(Ty::Record(Row {
            fields: field_tys,
            tail: Box::new(tail),
        }))
    }

    pub(super) fn infer_array_entries(
        &mut self,
        env: &TypeEnv,
        entries: &mut [ArrayEntry],
        expected: Option<Ty>,
        span: SourceSpan,
    ) -> Result<Ty, SpannedTypeError> {
        let expected_element = expected.as_ref().and_then(array_element_ty);
        let elt_ty = expected_element.clone().unwrap_or_else(|| self.fresh_ty());
        for entry in entries {
            match entry {
                ArrayEntry::Elem(expr) => {
                    let ty = if expected_element.is_some() {
                        self.infer_expr_expected(env, expr, elt_ty.clone())?
                    } else {
                        self.infer_expr(env, expr)?
                    };
                    unify(&mut self.subst, elt_ty.clone(), ty)?;
                }
                ArrayEntry::Spread(expr) => {
                    let expected_array =
                        Ty::App(Box::new(Ty::Con("Array".to_string())), vec![elt_ty.clone()]);
                    let ty = if expected_element.is_some() {
                        self.infer_expr_expected(env, expr, expected_array.clone())?
                    } else {
                        self.infer_expr(env, expr)?
                    };
                    unify(&mut self.subst, ty, expected_array)?;
                }
            }
        }
        let array_ty = Ty::App(Box::new(Ty::Con("Array".to_string())), vec![elt_ty]);
        if let Some(expected) = expected {
            unify(&mut self.subst, array_ty.clone(), expected).map_err(|err| err.at(span))?;
        }
        Ok(self.subst.apply(&array_ty))
    }
}

pub(super) fn combine_branch_types(
    subst: &mut Subst,
    left: Ty,
    right: Ty,
) -> Result<Ty, TypeError> {
    let left = subst.apply(&left);
    let right = subst.apply(&right);
    match (&left, &right) {
        _ if is_never(&left) && is_never(&right) => Ok(Ty::Never),
        _ if is_never(&left) => Ok(right),
        _ if is_never(&right) => Ok(left),
        _ => {
            unify(subst, left.clone(), right)?;
            Ok(subst.apply(&left))
        }
    }
}
