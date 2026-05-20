use crate::ast::{Pattern, SourceSpan};

#[derive(Debug, Clone)]
pub(super) struct MacroRuntimeError {
    pub(super) span: SourceSpan,
    pub(super) message: String,
    pub(super) related: Vec<MacroRuntimeRelated>,
}

#[derive(Debug, Clone)]
pub(super) struct MacroRuntimeRelated {
    pub(super) span: SourceSpan,
    pub(super) message: String,
}

impl MacroRuntimeError {
    pub(super) fn new(span: SourceSpan, message: impl Into<String>) -> Self {
        Self {
            span,
            message: message.into(),
            related: Vec::new(),
        }
    }

    pub(super) fn with_related(mut self, span: SourceSpan, message: impl Into<String>) -> Self {
        self.related.push(MacroRuntimeRelated {
            span,
            message: message.into(),
        });
        self
    }
}

pub(super) fn pattern_span(pattern: &Pattern) -> SourceSpan {
    match pattern {
        Pattern::Variable(_, span) => *span,
        Pattern::SyntaxQuote(pattern) => pattern.span(),
        _ => SourceSpan::synthetic(),
    }
}
