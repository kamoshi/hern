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
        match (start, end, inclusive) {
            (Some(start), Some(end), false) => {
                self.infer_int_range_bound(env, start, TypeMismatchContext::RangeStart)?;
                self.infer_int_range_bound(env, end, TypeMismatchContext::RangeEnd)?;
                Ok(range_ty("Range"))
            }
            (Some(start), Some(end), true) => {
                self.infer_int_range_bound(env, start, TypeMismatchContext::RangeStart)?;
                self.infer_int_range_bound(env, end, TypeMismatchContext::RangeEnd)?;
                Ok(range_ty("RangeInclusive"))
            }
            (Some(start), None, false) => {
                self.infer_int_range_bound(env, start, TypeMismatchContext::RangeStart)?;
                Ok(range_ty("RangeFrom"))
            }
            (Some(_), None, true) => {
                unreachable!("parser rejects inclusive ranges without end bounds")
            }
            (None, Some(end), false) => {
                self.infer_int_range_bound(env, end, TypeMismatchContext::RangeEnd)?;
                Ok(range_ty("RangeTo"))
            }
            (None, Some(end), true) => {
                self.infer_int_range_bound(env, end, TypeMismatchContext::RangeEnd)?;
                Ok(range_ty("RangeToInclusive"))
            }
            (None, None, false) => Ok(Ty::Con("RangeFull".to_string())),
            (None, None, true) => {
                unreachable!("parser rejects inclusive ranges without end bounds")
            }
        }
    }

    fn infer_int_range_bound(
        &mut self,
        env: &TypeEnv,
        expr: &mut Expr,
        context: TypeMismatchContext,
    ) -> Result<(), SpannedTypeError> {
        let ty = self.infer_expr(env, expr)?;
        unify(&mut self.subst, ty, Ty::Int)
            .map_err(|err| err.with_mismatch_context(context).at(expr.span))
    }

    pub(super) fn infer_record_expr(
        &mut self,
        env: &TypeEnv,
        entries: &mut [RecordEntry],
        _span: SourceSpan,
    ) -> Result<Ty, SpannedTypeError> {
        let mut field_tys: Vec<(String, Ty)> = Vec::new();
        let mut tail = Ty::Unit;
        for entry in entries {
            match entry {
                RecordEntry::Field(name, expr) => {
                    let ty = self.infer_expr(env, expr)?;
                    merge_record_field(&mut field_tys, name.clone(), ty)
                        .map_err(|err| err.at(expr.span))?;
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
                    )
                    .map_err(|err| err.at(expr.span))?;
                    let resolved_spread = self.subst.apply(&spread_ty);
                    let Ty::Record(row) = resolved_spread else {
                        return Err(TypeError::Mismatch {
                            expected: Ty::Record(Row {
                                fields: vec![],
                                tail: Box::new(self.fresh_ty()),
                            }),
                            got: resolved_spread,
                        }
                        .at(expr.span));
                    };
                    for (name, ty) in row.fields {
                        merge_record_field(&mut field_tys, name, ty)
                            .map_err(|err| err.at(expr.span))?;
                    }
                    tail = merge_record_spread_tail(&mut self.subst, tail, *row.tail)
                        .map_err(|err| err.at(expr.span))?;
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
                    unify(&mut self.subst, elt_ty.clone(), ty).map_err(|err| err.at(expr.span))?;
                }
                ArrayEntry::Spread(expr) => {
                    let expected_array = array_ty(elt_ty.clone());
                    let ty = if expected_element.is_some() {
                        self.infer_expr_expected(env, expr, expected_array.clone())?
                    } else {
                        self.infer_expr(env, expr)?
                    };
                    unify(&mut self.subst, ty, expected_array).map_err(|err| err.at(expr.span))?;
                }
            }
        }
        let array_ty = array_ty(elt_ty);
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
