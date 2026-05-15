use crate::ast::SourceSpan;
use crate::types::{Ty, display_ty_with_var_names, free_type_vars_in_display_order, type_var_name};
use std::collections::HashMap;
use std::fmt;

#[derive(Debug, Clone, PartialEq)]
pub enum TypeError {
    Mismatch(Ty, Ty),
    MismatchWithContext {
        context: Vec<TypeMismatchContext>,
        expected: Ty,
        got: Ty,
    },
    OccursCheck(crate::types::TyVar),
    UnboundVariable(String),
    ImmutableAssignment(String),
    ImmutablePlace(String),
    ExpectedMutablePlace(String),
    MutableParamMustBindName,
    MutableFunctionCapabilityMismatch,
    NotAFunction(Ty),
    ArityMismatch {
        expected: usize,
        got: usize,
    },
    TraitArityMismatch {
        trait_name: String,
        expected: usize,
        got: usize,
    },
    FunctionalDependencyViolation {
        trait_name: String,
        message: String,
    },
    InvalidTraitImplHead {
        trait_name: String,
        message: String,
    },
    InvalidTraitConstraint {
        trait_name: String,
        message: String,
    },
    InvalidAssignmentTarget,
    NonExhaustiveMatch {
        missing: String,
    },
    DuplicateOperator(String),
    MissingTraitMethod {
        trait_name: String,
        impl_target: String,
        method: String,
    },
    TraitMethodArityMismatch {
        trait_name: String,
        method: String,
        expected: usize,
        got: usize,
    },
    TraitMethodMissingTarget {
        trait_name: String,
        method: String,
    },
    DuplicateTypeTraitName(String),
    ExtraTraitMethod {
        trait_name: String,
        method: String,
    },
    BreakOutsideLoop,
    ContinueOutsideLoop,
    ReturnOutsideFunction,
    UnresolvedTrait {
        context: String,
        trait_name: String,
    },
    UnknownTrait(String),
    UnknownTraitMethod {
        trait_name: String,
        method: String,
    },
    UnknownImport(String),
    UnknownType(String),
    TypeAliasArityMismatch {
        name: String,
        expected: usize,
        got: usize,
    },
    RecursiveTypeAlias(String),
    MissingTraitImpl {
        trait_name: String,
        impl_target: String,
    },
    AmbiguousTraitMethod {
        method: String,
        candidates: Vec<String>,
    },
    UnknownMethod {
        receiver: String,
        method: String,
    },
    UnknownMethodWithCandidates {
        receiver: String,
        method: String,
        candidates: Vec<String>,
    },
    UnknownMethodOnUnresolvedArray {
        receiver: String,
        method: String,
        candidates: Vec<String>,
    },
    InvalidTraitImplTarget(String),
    UnknownAssociatedFunction {
        target: String,
        function: String,
    },
    AssociatedFunctionAsMethod {
        target: String,
        function: String,
    },
    MethodRequiresReceiver {
        target: String,
        method: String,
    },
    AmbiguousMethodReceiver {
        method: String,
    },
    InvalidInherentImplTarget(String),
    DuplicateInherentMethod {
        target: String,
        method: String,
    },
    InherentMethodMissingReceiver {
        target: String,
        method: String,
    },
    /// A refutable pattern was used in a function-parameter position.
    /// Only irrefutable patterns (variable, wildcard, record, `[..rest]`) are allowed.
    RefutableParamPattern,
    /// A refutable pattern was used in a `let` binding.
    /// Only irrefutable patterns are allowed here; use `match` for refutable ones.
    RefutableLetPattern,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TypeMismatchContext {
    FunctionParam(usize),
    FunctionReturn,
    TupleElement(usize),
    TypeArgument(usize),
    RecordField(String),
    RangeStart,
    RangeEnd,
}

#[derive(Debug, Clone, PartialEq)]
pub struct SpannedTypeError {
    pub span: Option<SourceSpan>,
    pub error: Box<TypeError>,
}

impl TypeError {
    pub fn at(self, span: SourceSpan) -> SpannedTypeError {
        SpannedTypeError {
            span: Some(span),
            error: Box::new(self),
        }
    }

    pub fn unspanned(self) -> SpannedTypeError {
        SpannedTypeError {
            span: None,
            error: Box::new(self),
        }
    }

    pub fn with_mismatch_context(self, context: TypeMismatchContext) -> Self {
        match self {
            TypeError::Mismatch(expected, got) => TypeError::MismatchWithContext {
                context: vec![context],
                expected,
                got,
            },
            TypeError::MismatchWithContext {
                context: mut inner,
                expected,
                got,
            } => {
                inner.insert(0, context);
                TypeError::MismatchWithContext {
                    context: inner,
                    expected,
                    got,
                }
            }
            other => other,
        }
    }
}

impl fmt::Display for TypeMismatchContext {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TypeMismatchContext::FunctionParam(index) => {
                write!(f, "function parameter {}", index + 1)
            }
            TypeMismatchContext::FunctionReturn => write!(f, "function return"),
            TypeMismatchContext::TupleElement(index) => write!(f, "tuple element {}", index + 1),
            TypeMismatchContext::TypeArgument(index) => write!(f, "type argument {}", index + 1),
            TypeMismatchContext::RecordField(name) => write!(f, "record field `{}`", name),
            TypeMismatchContext::RangeStart => write!(f, "range start bound"),
            TypeMismatchContext::RangeEnd => write!(f, "range end bound"),
        }
    }
}

impl SpannedTypeError {
    pub fn with_span_if_absent(mut self, span: SourceSpan) -> Self {
        if self.span.is_none() {
            self.span = Some(span);
        }
        self
    }
}

impl From<TypeError> for SpannedTypeError {
    fn from(error: TypeError) -> Self {
        error.unspanned()
    }
}

impl fmt::Display for SpannedTypeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.error.fmt(f)
    }
}

impl std::error::Error for SpannedTypeError {}

fn display_mismatch_types(expected: &Ty, got: &Ty) -> (String, String) {
    let mut vars = free_type_vars_in_display_order(expected);
    for var in free_type_vars_in_display_order(got) {
        if !vars.contains(&var) {
            vars.push(var);
        }
    }
    let names: HashMap<_, _> = vars
        .into_iter()
        .enumerate()
        .map(|(index, var)| (var, type_var_name(index)))
        .collect();
    (
        display_ty_with_var_names(expected, &names),
        display_ty_with_var_names(got, &names),
    )
}

impl fmt::Display for TypeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TypeError::Mismatch(t1, t2) => {
                let (expected, got) = display_mismatch_types(t1, t2);
                write!(f, "type mismatch: expected `{}`, got `{}`", expected, got)
            }
            TypeError::MismatchWithContext {
                context,
                expected,
                got,
            } => {
                write!(f, "type mismatch")?;
                if !context.is_empty() {
                    write!(f, " in ")?;
                    for (idx, item) in context.iter().enumerate() {
                        if idx > 0 {
                            write!(f, ", ")?;
                        }
                        write!(f, "{}", item)?;
                    }
                }
                let (expected, got) = display_mismatch_types(expected, got);
                write!(f, ": expected `{}`, got `{}`", expected, got)
            }
            TypeError::OccursCheck(v) => {
                write!(f, "infinite type: '{} occurs in its own definition", v)
            }
            TypeError::UnboundVariable(name) => write!(f, "unbound variable: `{}`", name),
            TypeError::ImmutableAssignment(name) => {
                write!(f, "cannot assign to immutable variable `{}`", name)
            }
            TypeError::ImmutablePlace(name) => {
                write!(
                    f,
                    "cannot mutate fields of `{}`: it is not an owned mutable place",
                    name
                )
            }
            TypeError::ExpectedMutablePlace(message) => write!(f, "{}", message),
            TypeError::MutableParamMustBindName => {
                write!(f, "mutable place parameters must bind a single name")
            }
            TypeError::MutableFunctionCapabilityMismatch => write!(
                f,
                "mutable function parameter requirements are incompatible with this function type"
            ),
            TypeError::NotAFunction(ty) => write!(f, "expected a function, got `{}`", ty),
            TypeError::ArityMismatch { expected, got } => {
                write!(
                    f,
                    "wrong number of arguments: expected {}, got {}",
                    expected, got
                )
            }
            TypeError::TraitArityMismatch {
                trait_name,
                expected,
                got,
            } => write!(
                f,
                "trait `{}` expects {} type argument{}, got {}",
                trait_name,
                expected,
                if *expected == 1 { "" } else { "s" },
                got
            ),
            TypeError::FunctionalDependencyViolation {
                trait_name,
                message,
            } => write!(
                f,
                "impl for `{}` violates functional dependency: {}",
                trait_name, message
            ),
            TypeError::InvalidTraitImplHead {
                trait_name,
                message,
            } => write!(
                f,
                "invalid impl head for trait `{}`: {}",
                trait_name, message
            ),
            TypeError::InvalidTraitConstraint {
                trait_name,
                message,
            } => write!(
                f,
                "invalid constraint for trait `{}`: {}",
                trait_name, message
            ),
            TypeError::InvalidAssignmentTarget => write!(f, "invalid assignment target"),
            TypeError::NonExhaustiveMatch { missing } => {
                write!(f, "non-exhaustive match: {}", missing)
            }
            TypeError::DuplicateOperator(op) => {
                write!(f, "operator `{}` is defined in multiple traits", op)
            }
            TypeError::MissingTraitMethod {
                trait_name,
                impl_target,
                method,
            } => write!(
                f,
                "impl {} for {} is missing method `{}`",
                trait_name, impl_target, method
            ),
            TypeError::TraitMethodArityMismatch {
                trait_name,
                method,
                expected,
                got,
            } => write!(
                f,
                "impl method `{}` for trait `{}` has wrong number of arguments: expected {}, got {}",
                method, trait_name, expected, got
            ),
            TypeError::TraitMethodMissingTarget { trait_name, method } => write!(
                f,
                "trait method `{}` in trait `{}` must have at least one parameter",
                method, trait_name
            ),
            TypeError::DuplicateTypeTraitName(name) => write!(
                f,
                "name `{}` is already defined as both a type and a trait in this scope",
                name
            ),
            TypeError::ExtraTraitMethod { trait_name, method } => {
                write!(
                    f,
                    "method `{}` is not defined in trait `{}`",
                    method, trait_name
                )
            }
            TypeError::BreakOutsideLoop => write!(f, "`break` outside of a loop"),
            TypeError::ContinueOutsideLoop => write!(f, "`continue` outside of a loop"),
            TypeError::ReturnOutsideFunction => write!(f, "`return` outside of a function"),
            TypeError::UnresolvedTrait {
                context,
                trait_name,
            } => write!(
                f,
                "could not resolve `{}` implementation for {} context",
                trait_name, context
            ),
            TypeError::UnknownTrait(name) => write!(f, "unknown trait: `{}`", name),
            TypeError::UnknownTraitMethod { trait_name, method } => {
                write!(f, "trait `{}` has no method `{}`", trait_name, method)
            }
            TypeError::UnknownImport(path) => write!(f, "unknown import: `{}`", path),
            TypeError::UnknownType(name) => write!(f, "unknown type: `{}`", name),
            TypeError::TypeAliasArityMismatch {
                name,
                expected,
                got,
            } => write!(
                f,
                "type alias `{}` expects {} type argument{}, got {}",
                name,
                expected,
                if *expected == 1 { "" } else { "s" },
                got
            ),
            TypeError::RecursiveTypeAlias(name) => write!(
                f,
                "recursive type alias `{}` is not supported; use a nominal type constructor instead",
                name
            ),
            TypeError::MissingTraitImpl {
                trait_name,
                impl_target,
            } => write!(
                f,
                "trait `{}` is not implemented for `{}`",
                trait_name, impl_target
            ),
            TypeError::AmbiguousTraitMethod { method, candidates } => write!(
                f,
                "ambiguous method `{}`: defined in multiple traits ({}); \
                 use explicit TraitName::{}() syntax to disambiguate",
                method,
                candidates.join(", "),
                method,
            ),
            TypeError::UnknownMethod { receiver, method } => {
                write!(f, "type `{}` has no method `{}`", receiver, method)
            }
            TypeError::UnknownMethodWithCandidates {
                receiver,
                method,
                candidates,
            } => {
                let note = if receiver.contains('\'') {
                    "; the receiver type is still unresolved"
                } else {
                    ""
                };
                write!(
                    f,
                    "type `{}` has no method `{}`{}; available candidates: {}",
                    receiver,
                    method,
                    note,
                    candidates.join(", ")
                )
            }
            TypeError::UnknownMethodOnUnresolvedArray {
                receiver,
                method,
                candidates,
            } => {
                write!(
                    f,
                    "type `{}` has no method `{}`; the array element type is unknown, so Hern cannot choose a specialized method; available candidates: {}; add an element type annotation such as `[int]` or `[float]`",
                    receiver,
                    method,
                    candidates.join(", ")
                )
            }
            TypeError::InvalidTraitImplTarget(target) => write!(
                f,
                "invalid trait impl target `{}`: expected a named type, type application, or tuple",
                target
            ),
            TypeError::UnknownAssociatedFunction { target, function } => {
                write!(
                    f,
                    "type `{}` has no associated function `{}`",
                    target, function
                )
            }
            TypeError::AssociatedFunctionAsMethod { target, function } => write!(
                f,
                "associated function `{}` for `{}` must be called with `{}::{}`",
                function, target, target, function
            ),
            TypeError::MethodRequiresReceiver { target, method } => write!(
                f,
                "method `{}` for `{}` requires a receiver; call it with `value.{}`",
                method, target, method
            ),
            TypeError::AmbiguousMethodReceiver { method } => write!(
                f,
                "cannot resolve method `{}` because the receiver type is unconstrained; add a type annotation",
                method
            ),
            TypeError::InvalidInherentImplTarget(target) => write!(
                f,
                "invalid inherent impl target `{}`: expected a nominal type or one of `string`, `int`, `float`, `bool`",
                target
            ),
            TypeError::DuplicateInherentMethod { target, method } => write!(
                f,
                "method `{}` is already defined for inherent impl target `{}`",
                method, target
            ),
            TypeError::InherentMethodMissingReceiver { target, method } => write!(
                f,
                "inherent method `{}` for `{}` must have a first receiver parameter",
                method, target
            ),
            TypeError::RefutableParamPattern => write!(
                f,
                "refutable pattern in function parameter: only variable, wildcard, record, and \
                 rest-list patterns are allowed here; use a match expression in the body instead"
            ),
            TypeError::RefutableLetPattern => write!(
                f,
                "refutable pattern in let binding: only variable, wildcard, record, tuple, and \
                 rest-list patterns are allowed here; use match instead"
            ),
        }
    }
}
