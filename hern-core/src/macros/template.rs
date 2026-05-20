use crate::syntax::{ScopeSet, Syntax, SyntaxKind, SyntaxOrigin, SyntaxTemplate};

use super::diagnostics::MacroRuntimeError;
use super::runtime::MacroRuntimeState;
use super::value::{MacroEnv, MacroValue};

pub(super) fn expand_template(
    template: &SyntaxTemplate,
    env: &MacroEnv,
    state: &mut MacroRuntimeState,
) -> Result<Syntax, MacroRuntimeError> {
    state.spend(template_span(template))?;
    match template {
        SyntaxTemplate::Token { token, span } => Ok(Syntax {
            kind: SyntaxKind::Token(token.clone()),
            span: *span,
            origin: SyntaxOrigin::Generated,
            scopes: ScopeSet::macro_introduction(state.macro_call_span()),
        }),
        SyntaxTemplate::Tree {
            delimiter,
            children,
            span,
        } => {
            let mut out = Vec::new();
            for child in children {
                match child {
                    SyntaxTemplate::Splice { name, repeat, span } => {
                        let value = env.get(name).ok_or_else(|| {
                            MacroRuntimeError::new(*span, format!("unknown splice `{name}`"))
                        })?;
                        if *repeat {
                            let MacroValue::SyntaxArray(items) = value else {
                                return Err(MacroRuntimeError::new(
                                    *span,
                                    format!("splice `{name}...` expects a repeated capture"),
                                ));
                            };
                            out.extend(items.clone());
                        } else {
                            let MacroValue::Syntax(syntax) = value else {
                                return Err(MacroRuntimeError::new(
                                    *span,
                                    format!("splice `{name}` expects Syntax"),
                                ));
                            };
                            out.push(syntax.clone());
                        }
                    }
                    other => out.push(expand_template(other, env, state)?),
                }
            }
            Ok(Syntax {
                kind: SyntaxKind::Tree {
                    delimiter: *delimiter,
                    children: out,
                },
                span: *span,
                origin: SyntaxOrigin::Generated,
                scopes: ScopeSet::macro_introduction(state.macro_call_span()),
            })
        }
        SyntaxTemplate::Splice { name, span, .. } => match env.get(name) {
            Some(MacroValue::Syntax(syntax)) => Ok(syntax.clone()),
            Some(_) => Err(MacroRuntimeError::new(
                *span,
                format!("splice `{name}` expects Syntax"),
            )),
            None => Err(MacroRuntimeError::new(
                *span,
                format!("unknown splice `{name}`"),
            )),
        },
    }
}

fn template_span(template: &SyntaxTemplate) -> crate::ast::SourceSpan {
    match template {
        SyntaxTemplate::Token { span, .. }
        | SyntaxTemplate::Tree { span, .. }
        | SyntaxTemplate::Splice { span, .. } => *span,
    }
}
