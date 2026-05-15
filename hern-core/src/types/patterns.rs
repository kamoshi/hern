use crate::ast::Pattern;
use crate::types::{Ty, TyVar, VariantEnv, error::TypeError};
use std::collections::HashSet;

/// Returns `true` if `pat` is irrefutable, i.e. always matches regardless of
/// the runtime value. Only irrefutable patterns may appear in function-parameter
/// position; refutable patterns must use a `match` expression in the body.
pub(super) fn is_irrefutable_param(pat: &Pattern, variant_env: &VariantEnv) -> bool {
    match pat {
        Pattern::Variable(..) | Pattern::Wildcard => true,
        // Only OPEN records (with a rest binding) are irrefutable for fn params.
        // A closed record like #{ x } is refutable at runtime.
        Pattern::Record { rest, .. } => rest.is_some(),
        Pattern::Tuple(elems) => elems.iter().all(|e| is_irrefutable_param(e, variant_env)),
        // An empty list pattern with a rest binding (`[..]` / `[..rest]`) matches
        // any list unconditionally. Any other list pattern requires a specific
        // length, so it is refutable.
        Pattern::List { elements, rest } => elements.is_empty() && rest.is_some(),
        // A constructor pattern is irrefutable when it is the sole variant of its
        // type — there is no other shape the value could have.
        Pattern::Constructor { name, .. } => is_sole_variant(name, variant_env),
        Pattern::StringLit(_) => false,
    }
}

/// Like `is_irrefutable_param` but used for `let` bindings, where any record
/// pattern is considered safe because the type system guarantees the value shape.
pub(super) fn is_irrefutable_let(pat: &Pattern, variant_env: &VariantEnv) -> bool {
    match pat {
        Pattern::Variable(..) | Pattern::Wildcard => true,
        Pattern::Record { .. } => true,
        Pattern::Tuple(elems) => elems.iter().all(|e| is_irrefutable_let(e, variant_env)),
        Pattern::List { elements, rest } => elements.is_empty() && rest.is_some(),
        Pattern::Constructor { name, .. } => is_sole_variant(name, variant_env),
        Pattern::StringLit(_) => false,
    }
}

/// Returns `true` if `constructor_name` is the only variant of its type.
fn is_sole_variant(constructor_name: &str, variant_env: &VariantEnv) -> bool {
    if let Some(info) = variant_env.0.get(constructor_name) {
        let type_name = &info.type_name;
        variant_env
            .0
            .values()
            .filter(|v| &v.type_name == type_name)
            .count()
            == 1
    } else {
        false
    }
}

/// Returns true if `p` is a catch-all pattern (no actual test at runtime).
pub(super) fn pattern_is_catch_all(p: &Pattern) -> bool {
    match p {
        Pattern::Wildcard | Pattern::Variable(_, _) => true,
        Pattern::Record { .. } => true,
        Pattern::Tuple(elems) => elems.iter().all(pattern_is_catch_all),
        Pattern::List {
            elements,
            rest: Some(_),
        } => elements.is_empty(),
        _ => false,
    }
}

pub(super) fn insert_pattern_bindings(scope: &mut HashSet<String>, pat: &Pattern) {
    match pat {
        Pattern::Variable(name, _) => {
            scope.insert(name.clone());
        }
        Pattern::Record { fields, rest } => {
            for (_, binding, _) in fields {
                if binding != "_" {
                    scope.insert(binding.clone());
                }
            }
            if let Some(Some((rest_name, _))) = rest {
                scope.insert(rest_name.clone());
            }
        }
        Pattern::List { elements, rest } => {
            for element in elements {
                insert_pattern_bindings(scope, element);
            }
            if let Some(Some((rest_name, _))) = rest {
                scope.insert(rest_name.clone());
            }
        }
        Pattern::Constructor { binding, .. } => {
            if let Some(binding) = binding {
                insert_pattern_bindings(scope, binding);
            }
        }
        Pattern::Tuple(elems) => {
            for elem in elems {
                insert_pattern_bindings(scope, elem);
            }
        }
        Pattern::Wildcard | Pattern::StringLit(_) => {}
    }
}

pub(super) fn check_exhaustive_match(
    patterns: &[&Pattern],
    scrutinee_ty: &Ty,
    variant_env: &VariantEnv,
) -> Result<(), TypeError> {
    if patterns.iter().any(|p| pattern_is_catch_all(p)) {
        return Ok(());
    }

    if array_element_ty(scrutinee_ty).is_some() {
        return check_array_exhaustive(patterns, scrutinee_ty, variant_env);
    }

    let Some(witnesses) = witness_patterns(scrutinee_ty, variant_env, 0) else {
        return Err(TypeError::NonExhaustiveMatch {
            missing: "non-exhaustive match — add a wildcard (_) arm".to_string(),
        });
    };

    if let Some(missing) = first_uncovered_witness(patterns, witnesses) {
        return Err(TypeError::NonExhaustiveMatch {
            missing: format!("missing pattern: {}", pattern_for_message(&missing)),
        });
    }

    Ok(())
}

fn first_uncovered_witness(patterns: &[&Pattern], witnesses: Vec<Pattern>) -> Option<Pattern> {
    witnesses.into_iter().find(|witness| {
        !patterns
            .iter()
            .any(|pattern| pattern_covers(pattern, witness))
    })
}

fn check_array_exhaustive(
    patterns: &[&Pattern],
    scrutinee_ty: &Ty,
    variant_env: &VariantEnv,
) -> Result<(), TypeError> {
    let open_lens: Vec<usize> = patterns
        .iter()
        .filter_map(|p| {
            if let Pattern::List {
                elements,
                rest: Some(_),
            } = p
            {
                Some(elements.len())
            } else {
                None
            }
        })
        .collect();

    if open_lens.is_empty() {
        return Err(TypeError::NonExhaustiveMatch {
            missing: "non-exhaustive: arrays longer than the matched lengths are not covered \
                     — add [head, ..] or _ arm"
                .to_string(),
        });
    }

    let element_ty = array_element_ty(scrutinee_ty).expect("array element type exists");
    let element_witnesses =
        witness_patterns(element_ty, variant_env, 0).unwrap_or_else(|| vec![Pattern::Wildcard]);
    let max_open = *open_lens.iter().max().unwrap();

    // List patterns only inspect a finite prefix. Cover every exact length below
    // the largest open prefix, then cover one open witness at that prefix length;
    // extensions of that final witness exercise all longer arrays.
    for len in 0..max_open {
        for candidate in list_witnesses_of_len(&element_witnesses, len, false) {
            if !patterns
                .iter()
                .any(|pattern| pattern_covers(pattern, &candidate))
            {
                return Err(TypeError::NonExhaustiveMatch {
                    missing: format!("missing pattern: {}", pattern_for_message(&candidate)),
                });
            }
        }
    }

    for candidate in list_witnesses_of_len(&element_witnesses, max_open, true) {
        if !patterns
            .iter()
            .any(|pattern| pattern_covers(pattern, &candidate))
        {
            return Err(TypeError::NonExhaustiveMatch {
                missing: format!("missing pattern: {}", pattern_for_message(&candidate)),
            });
        }
    }

    Ok(())
}

const MAX_WITNESS_DEPTH: usize = 4;
const MAX_WITNESSES: usize = 128;

fn list_witnesses_of_len(element_witnesses: &[Pattern], len: usize, open: bool) -> Vec<Pattern> {
    let mut product = vec![Vec::new()];
    for _ in 0..len {
        let mut next = Vec::new();
        for prefix in &product {
            for witness in element_witnesses {
                let mut row = prefix.clone();
                row.push(witness.clone());
                next.push(row);
                if next.len() > MAX_WITNESSES {
                    return vec![Pattern::List {
                        elements: vec![Pattern::Wildcard; len],
                        rest: open.then_some(None),
                    }];
                }
            }
        }
        product = next;
    }

    product
        .into_iter()
        .map(|elements| Pattern::List {
            elements,
            rest: open.then_some(None),
        })
        .collect()
}

fn witness_patterns(ty: &Ty, variant_env: &VariantEnv, depth: usize) -> Option<Vec<Pattern>> {
    if depth > MAX_WITNESS_DEPTH {
        return Some(vec![Pattern::Wildcard]);
    }

    match ty {
        Ty::Tuple(items) => {
            let mut product = vec![Vec::new()];
            for item_ty in items {
                let item_witnesses = witness_patterns(item_ty, variant_env, depth + 1)?;
                let mut next = Vec::new();
                for prefix in &product {
                    for witness in &item_witnesses {
                        let mut row = prefix.clone();
                        row.push(witness.clone());
                        next.push(row);
                        if next.len() > MAX_WITNESSES {
                            return Some(vec![Pattern::Wildcard]);
                        }
                    }
                }
                product = next;
            }
            Some(product.into_iter().map(Pattern::Tuple).collect())
        }
        Ty::App(con, args) if matches!(con.as_ref(), Ty::Con(name) if name == "Array") => {
            let elem_ty = args.first()?;
            let mut witnesses = vec![Pattern::List {
                elements: vec![],
                rest: None,
            }];
            for elem in witness_patterns(elem_ty, variant_env, depth + 1)? {
                witnesses.push(Pattern::List {
                    elements: vec![elem],
                    rest: Some(None),
                });
            }
            Some(witnesses)
        }
        Ty::Con(_) | Ty::App(_, _) => {
            let type_name = nominal_type_name(ty)?;
            if type_name == "Array" {
                return Some(vec![
                    Pattern::List {
                        elements: vec![],
                        rest: None,
                    },
                    Pattern::List {
                        elements: vec![Pattern::Wildcard],
                        rest: Some(None),
                    },
                ]);
            }

            let mut variants = variant_env
                .0
                .iter()
                .filter(|(_, info)| info.type_name == type_name)
                .collect::<Vec<_>>();
            if variants.is_empty() {
                return Some(vec![Pattern::Wildcard]);
            }
            variants.sort_by(|(left, _), (right, _)| left.cmp(right));

            let mut witnesses = Vec::new();
            for (variant_name, info) in variants {
                if let Some(payload_ty) = instantiated_payload_ty(ty, info) {
                    for payload in witness_patterns(&payload_ty, variant_env, depth + 1)
                        .unwrap_or_else(|| vec![Pattern::Wildcard])
                    {
                        witnesses.push(Pattern::Constructor {
                            name: variant_name.clone(),
                            binding: Some(Box::new(payload)),
                        });
                        if witnesses.len() > MAX_WITNESSES {
                            return Some(vec![Pattern::Wildcard]);
                        }
                    }
                } else {
                    witnesses.push(Pattern::Constructor {
                        name: variant_name.clone(),
                        binding: None,
                    });
                }
            }
            Some(witnesses)
        }
        Ty::Record(_)
        | Ty::Int
        | Ty::Float
        | Ty::Unit
        | Ty::Never
        | Ty::Var(_)
        | Ty::Func(_, _) => Some(vec![Pattern::Wildcard]),
        Ty::Qualified(_, inner) => witness_patterns(inner, variant_env, depth),
    }
}

fn pattern_covers(pattern: &Pattern, witness: &Pattern) -> bool {
    match pattern {
        Pattern::Wildcard | Pattern::Variable(_, _) | Pattern::Record { .. } => true,
        Pattern::StringLit(value) => matches!(witness, Pattern::StringLit(other) if value == other),
        Pattern::Constructor { name, binding } => {
            let Pattern::Constructor {
                name: witness_name,
                binding: witness_binding,
            } = witness
            else {
                return false;
            };
            if name != witness_name {
                return false;
            }
            match (binding.as_deref(), witness_binding.as_deref()) {
                (Some(pattern), Some(witness)) => pattern_covers(pattern, witness),
                // A bare constructor pattern covers every payload for that constructor.
                (None, _) => true,
                (Some(pattern), None) => pattern_covers(pattern, &Pattern::Wildcard),
            }
        }
        Pattern::Tuple(items) => {
            let Pattern::Tuple(witness_items) = witness else {
                return false;
            };
            items.len() == witness_items.len()
                && items
                    .iter()
                    .zip(witness_items)
                    .all(|(pattern, witness)| pattern_covers(pattern, witness))
        }
        Pattern::List { elements, rest } => {
            let Pattern::List {
                elements: witness_elements,
                rest: witness_rest,
            } = witness
            else {
                return false;
            };

            if rest.is_none() && witness_rest.is_some() {
                return false;
            }
            if rest.is_none() && elements.len() != witness_elements.len() {
                return false;
            }
            if rest.is_some() && elements.len() > witness_elements.len() {
                return false;
            }
            elements
                .iter()
                .zip(witness_elements)
                .all(|(pattern, witness)| pattern_covers(pattern, witness))
        }
    }
}

fn nominal_type_name(ty: &Ty) -> Option<&str> {
    match ty {
        Ty::Con(name) => Some(name),
        Ty::App(con, _) => match con.as_ref() {
            Ty::Con(name) => Some(name),
            _ => None,
        },
        _ => None,
    }
}

fn array_element_ty(ty: &Ty) -> Option<&Ty> {
    match ty {
        Ty::App(con, args) if matches!(con.as_ref(), Ty::Con(name) if name == "Array") => {
            args.first()
        }
        _ => None,
    }
}

fn instantiated_payload_ty(ty: &Ty, info: &crate::types::VariantInfo) -> Option<Ty> {
    let payload_ty = info.payload_ty.as_ref()?;
    let mut substitutions = Vec::new();
    if let Ty::App(_, args) = ty {
        substitutions.extend(
            info.type_param_vars
                .iter()
                .copied()
                .zip(args.iter().cloned()),
        );
    }
    Some(apply_variant_substitutions(payload_ty, &substitutions))
}

fn apply_variant_substitutions(ty: &Ty, substitutions: &[(TyVar, Ty)]) -> Ty {
    match ty {
        Ty::Var(var) => substitutions
            .iter()
            .find_map(|(from, to)| (*from == *var).then(|| to.clone()))
            .unwrap_or(Ty::Var(*var)),
        Ty::Qualified(constraints, inner) => Ty::Qualified(
            constraints.clone(),
            Box::new(apply_variant_substitutions(inner, substitutions)),
        ),
        Ty::Tuple(items) => Ty::Tuple(
            items
                .iter()
                .map(|item| apply_variant_substitutions(item, substitutions))
                .collect(),
        ),
        Ty::Func(params, ret) => Ty::Func(
            params
                .iter()
                .map(|param| crate::types::FuncParam {
                    ty: apply_variant_substitutions(&param.ty, substitutions),
                    capability: param.capability,
                })
                .collect(),
            crate::types::FuncReturn {
                ty: Box::new(apply_variant_substitutions(&ret.ty, substitutions)),
                capability: ret.capability,
            },
        ),
        Ty::App(con, args) => Ty::App(
            Box::new(apply_variant_substitutions(con, substitutions)),
            args.iter()
                .map(|arg| apply_variant_substitutions(arg, substitutions))
                .collect(),
        ),
        Ty::Record(row) => Ty::Record(crate::types::Row {
            fields: row
                .fields
                .iter()
                .map(|(name, ty)| (name.clone(), apply_variant_substitutions(ty, substitutions)))
                .collect(),
            tail: Box::new(apply_variant_substitutions(&row.tail, substitutions)),
        }),
        Ty::Int | Ty::Float | Ty::Unit | Ty::Never | Ty::Con(_) => ty.clone(),
    }
}

fn pattern_for_message(pattern: &Pattern) -> String {
    match pattern {
        Pattern::Wildcard => "_".to_string(),
        Pattern::Variable(name, _) => name.clone(),
        Pattern::StringLit(value) => format!("{value:?}"),
        Pattern::Constructor { name, binding } => match binding {
            Some(binding) => format!("{name}({})", pattern_for_message(binding)),
            None => name.clone(),
        },
        Pattern::Record { .. } => "#{ .. }".to_string(),
        Pattern::Tuple(items) => format!(
            "({})",
            items
                .iter()
                .map(pattern_for_message)
                .collect::<Vec<_>>()
                .join(", ")
        ),
        Pattern::List { elements, rest } => {
            let mut parts = elements.iter().map(pattern_for_message).collect::<Vec<_>>();
            if rest.is_some() {
                parts.push("..".to_string());
            }
            format!("[{}]", parts.join(", "))
        }
    }
}
