use crate::analysis::CompilerDiagnostic;
use crate::ast::{Expr, MacroDef, Param, Program, Stmt};
use std::collections::HashMap;

#[derive(Debug, Clone)]
pub(super) struct MacroRegistry {
    defs: HashMap<String, MacroDef>,
    helpers: HashMap<String, MacroHelperDef>,
}

impl MacroRegistry {
    pub(super) fn get(&self, name: &str) -> Option<&MacroDef> {
        self.defs.get(name)
    }

    pub(super) fn helpers(&self) -> HashMap<String, MacroHelperDef> {
        self.helpers.clone()
    }
}

#[derive(Debug, Clone)]
pub(super) struct MacroHelperDef {
    pub(super) name: String,
    pub(super) params: Vec<Param>,
    pub(super) body: Expr,
}

pub(super) fn collect_macros(program: &Program) -> Result<MacroRegistry, CompilerDiagnostic> {
    let mut defs = HashMap::new();
    let mut helpers = HashMap::new();
    for stmt in &program.stmts {
        match stmt {
            Stmt::Macro(def) => {
                if let Some(previous) = defs.insert(def.name.clone(), def.clone()) {
                    return Err(CompilerDiagnostic::error(
                        Some(def.name_span),
                        format!(
                            "duplicate macro `{}`; first defined at {}:{}",
                            def.name, previous.name_span.start_line, previous.name_span.start_col
                        ),
                    ));
                }
            }
            Stmt::Fn {
                name, params, body, ..
            } => {
                helpers
                    .entry(name.clone())
                    .or_insert_with(|| MacroHelperDef {
                        name: name.clone(),
                        params: params.clone(),
                        body: body.clone(),
                    });
            }
            _ => {}
        }
    }
    Ok(MacroRegistry { defs, helpers })
}
