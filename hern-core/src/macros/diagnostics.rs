use crate::ast::{Pattern, SourceSpan};

#[derive(Debug, Clone)]
pub(super) struct MacroRuntimeError {
    pub(super) span: SourceSpan,
    pub(super) message: String,
}

impl MacroRuntimeError {
    pub(super) fn new(span: SourceSpan, message: impl Into<String>) -> Self {
        Self {
            span,
            message: message.into(),
        }
    }
}

pub(super) fn pattern_span(pattern: &Pattern) -> SourceSpan {
    match pattern {
        Pattern::Variable(_, span) => *span,
        _ => SourceSpan::synthetic(),
    }
}
