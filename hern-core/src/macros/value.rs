use crate::syntax::Syntax;
use std::collections::HashMap;

use super::core_ir::CoreFunction;
use super::source::{syntax_shape_eq, syntax_source};

#[derive(Debug, Clone)]
pub(super) enum MacroValue {
    Unit,
    Int(i32),
    Float(f64),
    Bool(bool),
    String(String),
    Syntax(Syntax),
    SyntaxArray(Vec<Syntax>),
    Array(Vec<MacroValue>),
    Tuple(Vec<MacroValue>),
    Record(Vec<(String, MacroValue)>),
    OptionSome(Box<MacroValue>),
    OptionNone,
    Error(String),
    ResultOk(Box<MacroValue>),
    ResultErr(String),
    Closure(CoreFunction, MacroEnv),
    Break(Box<MacroValue>),
}

pub(super) type MacroEnv = HashMap<String, MacroValue>;

pub(super) fn macro_value_eq(lhs: &MacroValue, rhs: &MacroValue) -> Option<bool> {
    match (lhs, rhs) {
        (MacroValue::Unit, MacroValue::Unit) => Some(true),
        (MacroValue::Int(lhs), MacroValue::Int(rhs)) => Some(lhs == rhs),
        (MacroValue::Float(lhs), MacroValue::Float(rhs)) => Some(lhs == rhs),
        (MacroValue::Bool(lhs), MacroValue::Bool(rhs)) => Some(lhs == rhs),
        (MacroValue::String(lhs), MacroValue::String(rhs)) => Some(lhs == rhs),
        (MacroValue::Syntax(_), MacroValue::Syntax(_))
        | (MacroValue::SyntaxArray(_), MacroValue::SyntaxArray(_)) => {
            Some(macro_value_syntax_eq(lhs, rhs))
        }
        (MacroValue::Array(lhs), MacroValue::Array(rhs)) => {
            if lhs.len() != rhs.len() {
                return Some(false);
            }
            let mut equal = true;
            for (lhs, rhs) in lhs.iter().zip(rhs) {
                equal &= macro_value_eq(lhs, rhs)?;
            }
            Some(equal)
        }
        (MacroValue::Tuple(lhs), MacroValue::Tuple(rhs)) => {
            if lhs.len() != rhs.len() {
                return Some(false);
            }
            let mut equal = true;
            for (lhs, rhs) in lhs.iter().zip(rhs) {
                equal &= macro_value_eq(lhs, rhs)?;
            }
            Some(equal)
        }
        (MacroValue::Record(lhs), MacroValue::Record(rhs)) => {
            if lhs.len() != rhs.len() {
                return Some(false);
            }
            let mut equal = true;
            for (field, lhs_value) in lhs {
                let Some((_, rhs_value)) = rhs.iter().find(|(rhs_field, _)| rhs_field == field)
                else {
                    return Some(false);
                };
                equal &= macro_value_eq(lhs_value, rhs_value)?;
            }
            Some(equal)
        }
        (MacroValue::OptionNone, MacroValue::OptionNone) => Some(true),
        (MacroValue::OptionSome(lhs), MacroValue::OptionSome(rhs)) => macro_value_eq(lhs, rhs),
        (MacroValue::Closure(_, _), _) | (_, MacroValue::Closure(_, _)) => None,
        (MacroValue::Break(_), _) | (_, MacroValue::Break(_)) => None,
        _ => Some(false),
    }
}

pub(super) fn macro_value_to_string(value: &MacroValue) -> String {
    match value {
        MacroValue::Unit => "()".to_string(),
        MacroValue::Int(value) => value.to_string(),
        MacroValue::Float(value) => value.to_string(),
        MacroValue::Bool(value) => value.to_string(),
        MacroValue::String(value) => value.clone(),
        MacroValue::Syntax(syntax) => syntax_source(syntax),
        MacroValue::SyntaxArray(items) => items
            .iter()
            .map(syntax_source)
            .collect::<Vec<_>>()
            .join(", "),
        MacroValue::Array(items) => format!(
            "[{}]",
            items
                .iter()
                .map(macro_value_to_string)
                .collect::<Vec<_>>()
                .join(", ")
        ),
        MacroValue::Tuple(items) => format!(
            "({})",
            items
                .iter()
                .map(macro_value_to_string)
                .collect::<Vec<_>>()
                .join(", ")
        ),
        MacroValue::Record(fields) => format!(
            "#{{{}}}",
            fields
                .iter()
                .map(|(field, value)| format!("{field}: {}", macro_value_to_string(value)))
                .collect::<Vec<_>>()
                .join(", ")
        ),
        MacroValue::OptionSome(value) => format!("Some({})", macro_value_to_string(value)),
        MacroValue::OptionNone => "None".to_string(),
        MacroValue::Error(message) => format!("MacroError({message})"),
        MacroValue::ResultOk(value) => format!("Ok({})", macro_value_to_string(value)),
        MacroValue::ResultErr(message) => format!("Err({message})"),
        MacroValue::Closure(_, _) => "<function>".to_string(),
        MacroValue::Break(value) => format!("break {}", macro_value_to_string(value)),
    }
}

fn macro_value_syntax_eq(lhs: &MacroValue, rhs: &MacroValue) -> bool {
    match (lhs, rhs) {
        (MacroValue::Syntax(lhs), MacroValue::Syntax(rhs)) => syntax_shape_eq(lhs, rhs),
        (MacroValue::SyntaxArray(lhs), MacroValue::SyntaxArray(rhs)) => {
            lhs.len() == rhs.len()
                && lhs
                    .iter()
                    .zip(rhs)
                    .all(|(lhs, rhs)| syntax_shape_eq(lhs, rhs))
        }
        _ => false,
    }
}
