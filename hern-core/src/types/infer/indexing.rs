//! Inference for index expressions through the `Index` trait.
//!
//! Indexing is trait-dispatched rather than hard-coded on arrays. The receiver,
//! key, and output form the `Index<Receiver, Key, Output>` constraint, with the
//! receiver/key pair used to select a concrete dictionary when possible.

use super::*;

const INDEX_TRAIT_ARITY: usize = 3;

impl Infer {
    #[allow(clippy::too_many_arguments)]
    pub(super) fn infer_index_expr(
        &mut self,
        env: &TypeEnv,
        receiver: &mut Expr,
        key: &mut Expr,
        resolved_callee: &mut Option<ResolvedCallee>,
        pending_trait_method: &mut Option<(PendingDictArg, String)>,
        _dict_args: &mut Vec<DictRef>,
        _pending_dict_args: &mut Vec<PendingDictArg>,
    ) -> Result<Ty, SpannedTypeError> {
        let trait_def = self
            .traits
            .env
            .get("Index")
            .ok_or_else(|| TypeError::UnknownTrait("Index".to_string()))?
            .clone();
        if trait_def.params.len() != INDEX_TRAIT_ARITY {
            return Err(TypeError::TraitArityMismatch {
                trait_name: "Index".to_string(),
                expected: INDEX_TRAIT_ARITY,
                got: trait_def.params.len(),
            }
            .into());
        }
        let receiver_ty = self.infer_expr(env, receiver)?;
        let key_ty = self.infer_expr(env, key)?;
        let output_ty = Ty::Var(self.fresh_var());
        let args = [receiver_ty.clone(), key_ty.clone(), output_ty.clone()];
        let determinant_indexes = trait_dict_indexes(&trait_def);

        let resolved_args: Vec<Ty> = args.iter().map(|arg| self.subst.apply(arg)).collect();
        if let Some(output_ty) = self.resolve_multi_param_trait_dispatch(
            env,
            "Index",
            "index",
            resolved_args,
            determinant_indexes.clone(),
            vec![receiver_ty, key_ty],
            output_ty.clone(),
            resolved_callee,
            pending_trait_method,
            "Index dictionaries should be concrete",
        )? {
            return Ok(output_ty);
        }

        Err(TypeError::MissingTraitImpl {
            trait_name: "Index".to_string(),
            impl_target: format!(
                "{}, {}",
                self.subst.apply(&args[0]),
                self.subst.apply(&args[1])
            ),
        }
        .into())
    }
}
