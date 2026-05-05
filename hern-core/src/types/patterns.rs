use crate::ast::Pattern;
use std::collections::HashSet;

/// Returns `true` if `pat` is irrefutable, i.e. always matches regardless of
/// the runtime value. Only irrefutable patterns may appear in function-parameter
/// position; refutable patterns must use a `match` expression in the body.
pub(super) fn is_irrefutable_param(pat: &Pattern) -> bool {
    match pat {
        Pattern::Variable(..) | Pattern::Wildcard => true,
        // Only OPEN records (with a rest binding) are irrefutable for fn params.
        // A closed record like #{ x } is refutable at runtime.
        Pattern::Record { rest, .. } => rest.is_some(),
        Pattern::Tuple(elems) => elems.iter().all(is_irrefutable_param),
        // An empty list pattern with a rest binding (`[..]` / `[..rest]`) matches
        // any list unconditionally. Any other list pattern requires a specific
        // length, so it is refutable.
        Pattern::List { elements, rest } => elements.is_empty() && rest.is_some(),
        Pattern::Constructor { .. } | Pattern::StringLit(_) => false,
    }
}

/// Like `is_irrefutable_param` but used for `let` bindings, where any record
/// pattern is considered safe because the type system guarantees the value shape.
pub(super) fn is_irrefutable_let(pat: &Pattern) -> bool {
    match pat {
        Pattern::Variable(..) | Pattern::Wildcard => true,
        Pattern::Record { .. } => true,
        Pattern::Tuple(elems) => elems.iter().all(is_irrefutable_let),
        Pattern::List { elements, rest } => elements.is_empty() && rest.is_some(),
        Pattern::Constructor { .. } | Pattern::StringLit(_) => false,
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
            if let Some((binding, _)) = binding {
                scope.insert(binding.clone());
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
