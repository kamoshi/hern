use crate::ast::Pattern;
use crate::lex::NumberLiteral;
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
        Pattern::StringLit(_)
        | Pattern::NumberLit(_)
        | Pattern::BoolLit(_)
        | Pattern::SyntaxQuote(_)
        | Pattern::IntRange { .. } => false,
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
        Pattern::StringLit(_)
        | Pattern::NumberLit(_)
        | Pattern::BoolLit(_)
        | Pattern::SyntaxQuote(_)
        | Pattern::IntRange { .. } => false,
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
        Pattern::SyntaxQuote(pattern) => {
            let mut captures = Vec::new();
            crate::syntax::collect_syntax_pattern_captures(pattern, &mut captures);
            for capture in captures {
                scope.insert(capture.name);
            }
        }
        Pattern::Wildcard
        | Pattern::StringLit(_)
        | Pattern::NumberLit(_)
        | Pattern::BoolLit(_)
        | Pattern::IntRange { .. } => {}
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

    if let Some(missing) = first_uncovered_witness(patterns, witnesses.patterns) {
        return Err(TypeError::NonExhaustiveMatch {
            missing: missing_pattern_message(&missing, witnesses.approximate),
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
    let element_witnesses = witness_patterns(element_ty, variant_env, 0)
        .unwrap_or_else(|| WitnessSet::exact(vec![Pattern::Wildcard]));
    let max_open = *open_lens.iter().max().unwrap();

    // List patterns only inspect a finite prefix. Cover every exact length below
    // the largest open prefix, then cover one open witness at that prefix length;
    // extensions of that final witness exercise all longer arrays.
    for len in 0..max_open {
        let candidates = list_witnesses_of_len(&element_witnesses.patterns, len, false);
        let approximate = element_witnesses.approximate || candidates.approximate;
        for candidate in candidates.patterns {
            if !patterns
                .iter()
                .any(|pattern| pattern_covers(pattern, &candidate))
            {
                return Err(TypeError::NonExhaustiveMatch {
                    missing: missing_pattern_message(&candidate, approximate),
                });
            }
        }
    }

    let candidates = list_witnesses_of_len(&element_witnesses.patterns, max_open, true);
    let approximate = element_witnesses.approximate || candidates.approximate;
    for candidate in candidates.patterns {
        if !patterns
            .iter()
            .any(|pattern| pattern_covers(pattern, &candidate))
        {
            return Err(TypeError::NonExhaustiveMatch {
                missing: missing_pattern_message(&candidate, approximate),
            });
        }
    }

    Ok(())
}

const MAX_WITNESS_DEPTH: usize = 4;
// Witness generation is bounded. When a finite product grows beyond this cap,
// callers surface an approximation-limit diagnostic instead of pretending the
// wildcard-shaped fallback is a precise missing witness.
const MAX_WITNESSES: usize = 4096;

#[derive(Debug, Clone)]
struct WitnessSet {
    patterns: Vec<Pattern>,
    approximate: bool,
}

impl WitnessSet {
    fn exact(patterns: Vec<Pattern>) -> Self {
        Self {
            patterns,
            approximate: false,
        }
    }

    fn approximate(patterns: Vec<Pattern>) -> Self {
        Self {
            patterns,
            approximate: true,
        }
    }
}

fn missing_pattern_message(missing: &Pattern, approximate: bool) -> String {
    if approximate {
        format!(
            "missing pattern: {} (witness limit reached; add a wildcard (_) arm if the match is intentionally exhaustive)",
            pattern_for_message(missing)
        )
    } else {
        format!("missing pattern: {}", pattern_for_message(missing))
    }
}

fn list_witnesses_of_len(element_witnesses: &[Pattern], len: usize, open: bool) -> WitnessSet {
    let mut product = vec![Vec::new()];
    for _ in 0..len {
        let mut next = Vec::new();
        for prefix in &product {
            for witness in element_witnesses {
                let mut row = prefix.clone();
                row.push(witness.clone());
                next.push(row);
                if next.len() > MAX_WITNESSES {
                    return WitnessSet::approximate(vec![Pattern::List {
                        elements: vec![Pattern::Wildcard; len],
                        rest: open.then_some(None),
                    }]);
                }
            }
        }
        product = next;
    }

    WitnessSet::exact(
        product
            .into_iter()
            .map(|elements| Pattern::List {
                elements,
                rest: open.then_some(None),
            })
            .collect(),
    )
}

fn witness_patterns(ty: &Ty, variant_env: &VariantEnv, depth: usize) -> Option<WitnessSet> {
    if depth > MAX_WITNESS_DEPTH {
        return Some(WitnessSet::approximate(vec![Pattern::Wildcard]));
    }

    match ty {
        Ty::Tuple(items) => {
            let mut product = vec![Vec::new()];
            let mut approximate = false;
            for item_ty in items {
                let item_witnesses = witness_patterns(item_ty, variant_env, depth + 1)?;
                approximate |= item_witnesses.approximate;
                let mut next = Vec::new();
                for prefix in &product {
                    for witness in &item_witnesses.patterns {
                        let mut row = prefix.clone();
                        row.push(witness.clone());
                        next.push(row);
                        if next.len() > MAX_WITNESSES {
                            return Some(WitnessSet::approximate(vec![Pattern::Wildcard]));
                        }
                    }
                }
                product = next;
            }
            Some(WitnessSet {
                patterns: product.into_iter().map(Pattern::Tuple).collect(),
                approximate,
            })
        }
        Ty::App(con, args) if matches!(con.as_ref(), Ty::Con(name) if name == "Array") => {
            let elem_ty = args.first()?;
            let mut witnesses = vec![Pattern::List {
                elements: vec![],
                rest: None,
            }];
            let element_witnesses = witness_patterns(elem_ty, variant_env, depth + 1)?;
            for elem in element_witnesses.patterns {
                witnesses.push(Pattern::List {
                    elements: vec![elem],
                    rest: Some(None),
                });
            }
            Some(WitnessSet {
                patterns: witnesses,
                approximate: element_witnesses.approximate,
            })
        }
        Ty::Con(name) if name == "bool" => Some(WitnessSet::exact(vec![
            Pattern::BoolLit(true),
            Pattern::BoolLit(false),
        ])),
        Ty::Con(_) | Ty::App(_, _) => {
            let type_name = nominal_type_name(ty)?;
            if type_name == "Array" {
                return Some(WitnessSet::exact(vec![
                    Pattern::List {
                        elements: vec![],
                        rest: None,
                    },
                    Pattern::List {
                        elements: vec![Pattern::Wildcard],
                        rest: Some(None),
                    },
                ]));
            }

            let mut variants = variant_env
                .0
                .iter()
                .filter(|(_, info)| info.type_name == type_name)
                .collect::<Vec<_>>();
            if variants.is_empty() {
                return Some(WitnessSet::exact(vec![Pattern::Wildcard]));
            }
            variants.sort_by_key(|(variant_name, _)| *variant_name);

            let mut witnesses = Vec::new();
            let mut approximate = false;
            for (variant_name, info) in variants {
                if let Some(payload_ty) = instantiated_payload_ty(ty, info) {
                    let payload_witnesses = witness_patterns(&payload_ty, variant_env, depth + 1)
                        .unwrap_or_else(|| WitnessSet::exact(vec![Pattern::Wildcard]));
                    approximate |= payload_witnesses.approximate;
                    for payload in payload_witnesses.patterns {
                        witnesses.push(Pattern::Constructor {
                            name: variant_name.clone(),
                            binding: Some(Box::new(payload)),
                        });
                        if witnesses.len() > MAX_WITNESSES {
                            return Some(WitnessSet::approximate(vec![Pattern::Wildcard]));
                        }
                    }
                } else {
                    witnesses.push(Pattern::Constructor {
                        name: variant_name.clone(),
                        binding: None,
                    });
                }
            }
            Some(WitnessSet {
                patterns: witnesses,
                approximate,
            })
        }
        Ty::Never => Some(WitnessSet::exact(vec![])),
        Ty::Record(_) | Ty::Int | Ty::Float | Ty::Unit | Ty::Var(_) | Ty::Func(_, _) => {
            Some(WitnessSet::exact(vec![Pattern::Wildcard]))
        }
        Ty::Qualified(_, inner) => witness_patterns(inner, variant_env, depth),
    }
}

fn pattern_covers(pattern: &Pattern, witness: &Pattern) -> bool {
    match pattern {
        Pattern::Wildcard | Pattern::Variable(_, _) | Pattern::Record { .. } => true,
        Pattern::StringLit(value) => matches!(witness, Pattern::StringLit(other) if value == other),
        Pattern::NumberLit(value) => {
            matches!(witness, Pattern::NumberLit(other) if number_literals_equal(value, other))
        }
        Pattern::BoolLit(value) => matches!(witness, Pattern::BoolLit(other) if value == other),
        Pattern::SyntaxQuote(_) => false,
        Pattern::IntRange {
            start,
            end,
            inclusive,
        } => {
            let Pattern::NumberLit(NumberLiteral::Int(value)) = witness else {
                return false;
            };
            if *inclusive {
                value >= start && value <= end
            } else {
                value >= start && value < end
            }
        }
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

fn number_literals_equal(left: &NumberLiteral, right: &NumberLiteral) -> bool {
    match (left, right) {
        (NumberLiteral::Int(left), NumberLiteral::Int(right)) => left == right,
        (NumberLiteral::Float(left), NumberLiteral::Float(right)) => left == right,
        _ => false,
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
        Pattern::NumberLit(value) => value.as_lua_source(),
        Pattern::BoolLit(value) => value.to_string(),
        Pattern::IntRange {
            start,
            end,
            inclusive,
        } => {
            let op = if *inclusive { "..=" } else { ".." };
            format!("{start}{op}{end}")
        }
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
        Pattern::SyntaxQuote(_) => "`'(...)`".to_string(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn witness_limit_diagnostic_mentions_approximation() {
        let tuple_ty = Ty::Tuple(vec![Ty::Con("bool".to_string()); 13]);
        let err = check_exhaustive_match(&[], &tuple_ty, &VariantEnv::default())
            .expect_err("empty match should be non-exhaustive");

        assert!(matches!(
            err,
            TypeError::NonExhaustiveMatch { missing } if missing.contains("witness limit reached")
        ));
    }

    #[test]
    fn exhaustive_large_bool_product_under_cap_is_accepted() {
        let tuple_ty = Ty::Tuple(vec![Ty::Con("bool".to_string()); 8]);
        let patterns = bool_tuple_patterns(8);
        let pattern_refs = patterns.iter().collect::<Vec<_>>();

        check_exhaustive_match(&pattern_refs, &tuple_ty, &VariantEnv::default())
            .expect("all boolean tuple combinations should be exhaustive");
    }

    fn bool_tuple_patterns(width: usize) -> Vec<Pattern> {
        (0..(1usize << width))
            .map(|bits| {
                Pattern::Tuple(
                    (0..width)
                        .map(|idx| Pattern::BoolLit((bits & (1 << idx)) != 0))
                        .collect(),
                )
            })
            .collect()
    }
}
