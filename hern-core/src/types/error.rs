use crate::ast::SourceSpan;
use crate::types::Ty;
use std::fmt;

#[derive(Debug, Clone, PartialEq)]
pub enum TypeError {
    Mismatch(Ty, Ty),
    OccursCheck(crate::types::TyVar),
    UnboundVariable(String),
    ImmutableAssignment(String),
    NotAFunction(Ty),
    ArityMismatch {
        expected: usize,
        got: usize,
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

#[derive(Debug, Clone, PartialEq)]
pub struct SpannedTypeError {
    pub span: Option<SourceSpan>,
    pub error: TypeError,
}

impl TypeError {
    pub fn at(self, span: SourceSpan) -> SpannedTypeError {
        SpannedTypeError {
            span: Some(span),
            error: self,
        }
    }

    pub fn unspanned(self) -> SpannedTypeError {
        SpannedTypeError {
            span: None,
            error: self,
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

impl fmt::Display for TypeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TypeError::Mismatch(t1, t2) => {
                write!(f, "type mismatch: expected `{}`, got `{}`", t1, t2)
            }
            TypeError::OccursCheck(v) => {
                write!(f, "infinite type: '{}  occurs in its own definition", v)
            }
            TypeError::UnboundVariable(name) => write!(f, "unbound variable: `{}`", name),
            TypeError::ImmutableAssignment(name) => {
                write!(f, "cannot assign to immutable variable `{}`", name)
            }
            TypeError::NotAFunction(ty) => write!(f, "expected a function, got `{}`", ty),
            TypeError::ArityMismatch { expected, got } => {
                write!(
                    f,
                    "wrong number of arguments: expected {}, got {}",
                    expected, got
                )
            }
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
                 use explicit TraitName.{}() syntax to disambiguate",
                method,
                candidates.join(", "),
                method,
            ),
            TypeError::UnknownMethod { receiver, method } => {
                write!(f, "type `{}` has no method `{}`", receiver, method)
            }
            TypeError::AmbiguousMethodReceiver { method } => write!(
                f,
                "cannot resolve method `{}` because the receiver type is unconstrained; add a type annotation",
                method
            ),
            TypeError::InvalidInherentImplTarget(target) => write!(
                f,
                "invalid inherent impl target `{}`: expected a nominal type or one of `string`, `f64`, `bool`",
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
