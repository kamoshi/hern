use crate::analysis::CompilerDiagnostic;
use crate::ast::{Expr, MacroDef, Param, Program, Stmt};
use std::collections::HashMap;

#[derive(Debug, Clone)]
pub(super) struct MacroRegistry {
    defs: HashMap<String, MacroEntry>,
}

impl MacroRegistry {
    pub(super) fn get(&self, name: &str) -> Option<&MacroEntry> {
        self.defs.get(name)
    }
}

#[derive(Debug, Clone)]
pub(super) struct MacroHelperDef {
    pub(super) name: String,
    pub(super) params: Vec<Param>,
    pub(super) body: Expr,
}

#[derive(Debug, Clone)]
pub(super) struct MacroEntry {
    pub(super) def: MacroDef,
    pub(super) helpers: HashMap<String, MacroHelperDef>,
}

pub(super) fn collect_macros(program: &Program) -> Result<MacroRegistry, CompilerDiagnostic> {
    collect_macros_with_imports(program, std::iter::empty())
}

pub fn collect_exported_macro_names(program: &Program) -> Vec<String> {
    let mut names = program
        .stmts
        .iter()
        .filter_map(|stmt| match stmt {
            Stmt::Macro(def) => Some(def.name.clone()),
            _ => None,
        })
        .collect::<Vec<_>>();
    names.sort();
    names.dedup();
    names
}

pub(super) fn collect_macros_with_imports<'a>(
    program: &Program,
    imports: impl IntoIterator<Item = (&'a str, &'a Program)>,
) -> Result<MacroRegistry, CompilerDiagnostic> {
    let mut defs = HashMap::new();
    let local_helpers = collect_helpers(program);
    for stmt in &program.stmts {
        if let Stmt::Macro(def) = stmt {
            if let Some(previous) = defs.insert(
                def.name.clone(),
                MacroEntry {
                    def: def.clone(),
                    helpers: local_helpers.clone(),
                },
            ) {
                return Err(CompilerDiagnostic::error(
                    Some(def.name_span),
                    format!(
                        "duplicate macro `{}`; first defined at {}:{}",
                        def.name,
                        previous.def.name_span.start_line,
                        previous.def.name_span.start_col
                    ),
                ));
            }
        }
    }

    let mut owners = defs
        .keys()
        .map(|name| (name.clone(), "current module".to_string()))
        .collect::<HashMap<_, _>>();
    for (module_name, imported) in imports {
        let imported_helpers = collect_helpers(imported);
        for stmt in &imported.stmts {
            let Stmt::Macro(def) = stmt else {
                continue;
            };
            if let Some(owner) = owners.get(&def.name) {
                return Err(CompilerDiagnostic::error(
                    Some(def.name_span),
                    format!(
                        "macro `{}` imported from module `{}` conflicts with macro from {}",
                        def.name, module_name, owner
                    ),
                ));
            }
            owners.insert(def.name.clone(), format!("module `{module_name}`"));
            defs.insert(
                def.name.clone(),
                MacroEntry {
                    def: def.clone(),
                    helpers: imported_helpers.clone(),
                },
            );
        }
    }

    Ok(MacroRegistry { defs })
}

fn collect_helpers(program: &Program) -> HashMap<String, MacroHelperDef> {
    let mut helpers = HashMap::new();
    for stmt in &program.stmts {
        if let Stmt::Fn {
            name, params, body, ..
        } = stmt
        {
            helpers
                .entry(name.clone())
                .or_insert_with(|| MacroHelperDef {
                    name: name.clone(),
                    params: params.clone(),
                    body: body.clone(),
                });
        }
    }
    helpers
}
