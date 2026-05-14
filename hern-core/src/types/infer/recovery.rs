use crate::ast::{Expr, ExprKind, Pattern, Stmt, Type};
use crate::types::patterns::insert_pattern_bindings;
use std::collections::HashSet;

/// Top-level names tracked for recovery decisions.
///
/// Value, type, and trait namespaces are kept separate so a failed declaration does not suppress
/// an unrelated declaration with the same spelling in another namespace.
#[derive(Debug, Clone, Default)]
pub(super) struct CollectedNames {
    values: HashSet<String>,
    types: HashSet<String>,
    traits: HashSet<String>,
}

impl CollectedNames {
    pub(super) fn extend(&mut self, other: Self) {
        self.values.extend(other.values);
        self.types.extend(other.types);
        self.traits.extend(other.traits);
    }

    pub(super) fn overlaps(&self, other: &Self) -> bool {
        self.values.iter().any(|name| other.values.contains(name))
            || self.types.iter().any(|name| other.types.contains(name))
            || self.traits.iter().any(|name| other.traits.contains(name))
    }

    pub(super) fn remove_all(&mut self, other: &Self) {
        self.values.retain(|name| !other.values.contains(name));
        self.types.retain(|name| !other.types.contains(name));
        self.traits.retain(|name| !other.traits.contains(name));
    }
}

pub(super) fn stmt_bound_names(stmt: &Stmt) -> CollectedNames {
    let mut names = CollectedNames::default();
    match stmt {
        Stmt::Let { pat, .. } => {
            insert_pattern_bindings(&mut names.values, pat);
        }
        Stmt::Fn { name, .. } | Stmt::Op { name, .. } | Stmt::Extern { name, .. } => {
            names.values.insert(name.clone());
        }
        Stmt::Type(td) => {
            names.types.insert(td.name.clone());
            names
                .values
                .extend(td.variants.iter().map(|variant| variant.name.clone()));
        }
        Stmt::TypeAlias { name, .. } => {
            names.types.insert(name.clone());
        }
        Stmt::Trait(td) => {
            names.traits.insert(td.name.clone());
        }
        Stmt::Impl(id) => {
            names.traits.insert(id.trait_name.clone());
        }
        Stmt::InherentImpl(_) | Stmt::Expr(_) => {}
    }
    names
}

pub(super) fn stmt_referenced_names(stmt: &Stmt) -> CollectedNames {
    let mut refs = CollectedNames::default();
    collect_stmt_referenced_names(stmt, &mut refs, &HashSet::new(), &HashSet::new());
    refs
}

fn collect_stmt_referenced_names(
    stmt: &Stmt,
    refs: &mut CollectedNames,
    value_scope: &HashSet<String>,
    type_scope: &HashSet<String>,
) {
    match stmt {
        Stmt::Let { ty, value, .. } => {
            if let Some(ty) = ty {
                collect_type_referenced_names(ty, refs, type_scope);
            }
            collect_expr_referenced_names(value, refs, value_scope, type_scope);
        }
        Stmt::Fn {
            name,
            params,
            ret_type,
            body,
            ..
        } => {
            let mut body_scope = value_scope.clone();
            body_scope.insert(name.clone());
            for param in params {
                if let Some(param_ty) = &param.ty {
                    collect_type_referenced_names(param_ty, refs, type_scope);
                }
                insert_pattern_bindings(&mut body_scope, &param.pat);
            }
            if let Some(ret_type) = ret_type {
                collect_type_referenced_names(&ret_type.ty, refs, type_scope);
            }
            collect_expr_referenced_names(body, refs, &body_scope, type_scope);
        }
        Stmt::Op {
            params,
            ret_type,
            body,
            ..
        } => {
            let mut body_scope = value_scope.clone();
            for param in params {
                if let Some(param_ty) = &param.ty {
                    collect_type_referenced_names(param_ty, refs, type_scope);
                }
                insert_pattern_bindings(&mut body_scope, &param.pat);
            }
            if let Some(ret_type) = ret_type {
                collect_type_referenced_names(&ret_type.ty, refs, type_scope);
            }
            collect_expr_referenced_names(body, refs, &body_scope, type_scope);
        }
        Stmt::Trait(td) => {
            for method in &td.methods {
                for (_, param_ty) in &method.params {
                    collect_type_referenced_names(param_ty, refs, type_scope);
                }
                collect_type_referenced_names(&method.ret_type, refs, type_scope);
            }
        }
        Stmt::Impl(id) => {
            for arg in &id.trait_args {
                collect_type_referenced_names(arg, refs, type_scope);
            }
            for method in &id.methods {
                let mut method_scope = value_scope.clone();
                for param in &method.params {
                    if let Some(param_ty) = &param.ty {
                        collect_type_referenced_names(param_ty, refs, type_scope);
                    }
                    insert_pattern_bindings(&mut method_scope, &param.pat);
                }
                if let Some(ret_type) = &method.ret_type {
                    collect_type_referenced_names(&ret_type.ty, refs, type_scope);
                }
                collect_expr_referenced_names(&method.body, refs, &method_scope, type_scope);
            }
        }
        Stmt::InherentImpl(id) => {
            collect_type_referenced_names(&id.target, refs, type_scope);
            let mut impl_type_scope = type_scope.clone();
            impl_type_scope.insert("Self".to_string());
            for bound in &id.type_bounds {
                for trait_name in &bound.traits {
                    if !impl_type_scope.contains(trait_name) {
                        refs.types.insert(trait_name.clone());
                    }
                }
            }
            for method in &id.methods {
                let mut method_scope = value_scope.clone();
                let method_type_scope = impl_type_scope.clone();
                for bound in &method.type_bounds {
                    for trait_name in &bound.traits {
                        if !method_type_scope.contains(trait_name) {
                            refs.types.insert(trait_name.clone());
                        }
                    }
                }
                for param in &method.params {
                    if let Some(param_ty) = &param.ty {
                        collect_type_referenced_names(param_ty, refs, &method_type_scope);
                    }
                    insert_pattern_bindings(&mut method_scope, &param.pat);
                }
                if let Some(ret_type) = &method.ret_type {
                    collect_type_referenced_names(&ret_type.ty, refs, &method_type_scope);
                }
                collect_expr_referenced_names(
                    &method.body,
                    refs,
                    &method_scope,
                    &method_type_scope,
                );
            }
        }
        Stmt::Type(td) => {
            let mut stmt_type_scope = type_scope.clone();
            stmt_type_scope.insert(td.name.clone());
            for variant in &td.variants {
                if let Some(payload) = &variant.payload {
                    collect_type_referenced_names(payload, refs, &stmt_type_scope);
                }
            }
        }
        Stmt::TypeAlias { name, ty, .. } => {
            let mut stmt_type_scope = type_scope.clone();
            stmt_type_scope.insert(name.clone());
            collect_type_referenced_names(ty, refs, &stmt_type_scope);
        }
        Stmt::Extern { ty, .. } => collect_type_referenced_names(ty, refs, type_scope),
        Stmt::Expr(expr) => collect_expr_referenced_names(expr, refs, value_scope, type_scope),
    }
}

fn collect_expr_referenced_names(
    expr: &Expr,
    refs: &mut CollectedNames,
    value_scope: &HashSet<String>,
    type_scope: &HashSet<String>,
) {
    match &expr.kind {
        ExprKind::Number(_)
        | ExprKind::StringLit(_)
        | ExprKind::Bool(_)
        | ExprKind::Import(_)
        | ExprKind::Unit
        | ExprKind::Break(None)
        | ExprKind::Continue
        | ExprKind::Return(None) => {}
        ExprKind::Ident(name) => {
            if !value_scope.contains(name) {
                refs.values.insert(name.clone());
            }
        }
        ExprKind::Grouped(expr)
        | ExprKind::Not(expr)
        | ExprKind::Loop(expr)
        | ExprKind::Break(Some(expr))
        | ExprKind::Return(Some(expr)) => {
            collect_expr_referenced_names(expr, refs, value_scope, type_scope);
        }
        ExprKind::FieldAccess { expr, .. } => {
            if let ExprKind::Ident(name) = &expr.kind {
                refs.traits.insert(name.clone());
            }
            collect_expr_referenced_names(expr, refs, value_scope, type_scope);
        }
        ExprKind::AssociatedAccess { target, .. } => {
            collect_type_referenced_names(target, refs, type_scope);
        }
        ExprKind::Index { receiver, key, .. } => {
            collect_expr_referenced_names(receiver, refs, value_scope, type_scope);
            collect_expr_referenced_names(key, refs, value_scope, type_scope);
        }
        ExprKind::Assign { target, value }
        | ExprKind::Binary {
            lhs: target,
            rhs: value,
            ..
        } => {
            collect_expr_referenced_names(target, refs, value_scope, type_scope);
            collect_expr_referenced_names(value, refs, value_scope, type_scope);
        }
        ExprKind::Call { callee, args, .. } => {
            collect_expr_referenced_names(callee, refs, value_scope, type_scope);
            for arg in args {
                collect_expr_referenced_names(arg, refs, value_scope, type_scope);
            }
        }
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
        } => {
            collect_expr_referenced_names(cond, refs, value_scope, type_scope);
            collect_expr_referenced_names(then_branch, refs, value_scope, type_scope);
            collect_expr_referenced_names(else_branch, refs, value_scope, type_scope);
        }
        ExprKind::Match { scrutinee, arms } => {
            collect_expr_referenced_names(scrutinee, refs, value_scope, type_scope);
            for (pattern, body) in arms {
                collect_pattern_referenced_names(pattern, refs);
                let mut arm_scope = value_scope.clone();
                insert_pattern_bindings(&mut arm_scope, pattern);
                collect_expr_referenced_names(body, refs, &arm_scope, type_scope);
            }
        }
        ExprKind::Block { stmts, final_expr } => {
            let mut block_value_scope = value_scope.clone();
            let mut block_type_scope = type_scope.clone();
            for stmt in stmts {
                collect_stmt_referenced_names(stmt, refs, &block_value_scope, &block_type_scope);
                let bindings = stmt_bound_names(stmt);
                block_value_scope.extend(bindings.values);
                block_type_scope.extend(bindings.types);
            }
            if let Some(expr) = final_expr {
                collect_expr_referenced_names(expr, refs, &block_value_scope, &block_type_scope);
            }
        }
        ExprKind::Tuple(items) => {
            for item in items {
                collect_expr_referenced_names(item, refs, value_scope, type_scope);
            }
        }
        ExprKind::Array(entries) => {
            for entry in entries {
                collect_expr_referenced_names(entry.expr(), refs, value_scope, type_scope);
            }
        }
        ExprKind::Record(entries) => {
            for entry in entries {
                collect_expr_referenced_names(entry.expr(), refs, value_scope, type_scope);
            }
        }
        ExprKind::Lambda { params, body, .. } => {
            let mut lambda_scope = value_scope.clone();
            for param in params {
                if let Some(param_ty) = &param.ty {
                    collect_type_referenced_names(param_ty, refs, type_scope);
                }
                insert_pattern_bindings(&mut lambda_scope, &param.pat);
            }
            collect_expr_referenced_names(body, refs, &lambda_scope, type_scope);
        }
        ExprKind::For {
            pat,
            iterable,
            body,
            ..
        } => {
            collect_expr_referenced_names(iterable, refs, value_scope, type_scope);
            collect_pattern_referenced_names(pat, refs);
            let mut body_scope = value_scope.clone();
            insert_pattern_bindings(&mut body_scope, pat);
            collect_expr_referenced_names(body, refs, &body_scope, type_scope);
        }
    }
}

fn collect_type_referenced_names(
    ty: &Type,
    refs: &mut CollectedNames,
    type_scope: &HashSet<String>,
) {
    match ty {
        Type::Ident(name) => {
            if !type_scope.contains(name) {
                refs.types.insert(name.clone());
            }
        }
        Type::App(con, args) => {
            collect_type_referenced_names(con, refs, type_scope);
            for arg in args {
                collect_type_referenced_names(arg, refs, type_scope);
            }
        }
        Type::Func(params, ret) => {
            for param in params {
                collect_type_referenced_names(&param.ty, refs, type_scope);
            }
            collect_type_referenced_names(&ret.ty, refs, type_scope);
        }
        Type::Tuple(items) => {
            for item in items {
                collect_type_referenced_names(item, refs, type_scope);
            }
        }
        Type::Record(fields, _) => {
            for (_, field_ty) in fields {
                collect_type_referenced_names(field_ty, refs, type_scope);
            }
        }
        Type::Var(_) | Type::Unit | Type::Never | Type::Hole => {}
    }
}

fn collect_pattern_referenced_names(pat: &Pattern, refs: &mut CollectedNames) {
    match pat {
        Pattern::Constructor { name, .. } => {
            refs.values.insert(name.clone());
        }
        Pattern::List { elements, .. } | Pattern::Tuple(elements) => {
            for element in elements {
                collect_pattern_referenced_names(element, refs);
            }
        }
        Pattern::Wildcard
        | Pattern::StringLit(_)
        | Pattern::Variable(_, _)
        | Pattern::Record { .. } => {}
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{Expr, ExprKind, Stmt};

    #[test]
    fn unary_value_expressions_do_not_record_trait_references() {
        let stmt = Stmt::Expr(Expr::synthetic(ExprKind::Not(Box::new(Expr::synthetic(
            ExprKind::Ident("foo".to_string()),
        )))));

        let refs = stmt_referenced_names(&stmt);

        assert!(refs.values.contains("foo"));
        assert!(!refs.traits.contains("foo"));
    }
}
