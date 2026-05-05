use super::uri::{source_span_to_range, uri_to_path};
use super::workspace::load_document_graph_recovering;
use hern_core::ast::{
    ExternKind, ImplDef, InherentImplDef, Pattern, Program, SourceSpan, Stmt, TraitDef, TypeDef,
};
use lsp_types::{DocumentSymbol, DocumentSymbolResponse, SymbolKind, Uri};

pub(crate) fn document_symbols(
    state: &super::state::ServerState,
    uri: Uri,
) -> Option<DocumentSymbolResponse> {
    let path = uri_to_path(&uri)?;
    let graph = load_document_graph_recovering(state, &uri)?;
    let (_, program) = graph.module_for_path(&path)?;
    Some(DocumentSymbolResponse::Nested(symbols_for_program(program)))
}

fn symbols_for_program(program: &Program) -> Vec<DocumentSymbol> {
    program.stmts.iter().flat_map(symbols_for_stmt).collect()
}

fn symbols_for_stmt(stmt: &Stmt) -> Vec<DocumentSymbol> {
    match stmt {
        Stmt::Let { span, pat, .. } => pattern_binding_symbols(pat, *span),
        Stmt::Fn {
            span,
            name,
            name_span,
            ..
        } => vec![symbol(
            name.clone(),
            SymbolKind::FUNCTION,
            *span,
            *name_span,
            None,
        )],
        Stmt::Op {
            span,
            name,
            name_span,
            ..
        } => vec![symbol(
            name.clone(),
            SymbolKind::OPERATOR,
            *span,
            *name_span,
            None,
        )],
        Stmt::Trait(trait_def) => vec![trait_symbol(trait_def)],
        Stmt::Impl(impl_def) => vec![impl_symbol(impl_def)],
        Stmt::InherentImpl(impl_def) => vec![inherent_impl_symbol(impl_def)],
        Stmt::Type(type_def) => vec![type_symbol(type_def)],
        Stmt::TypeAlias {
            span,
            name,
            name_span,
            ..
        } => vec![symbol(
            name.clone(),
            SymbolKind::STRUCT,
            *span,
            *name_span,
            None,
        )],
        Stmt::Extern {
            span,
            name,
            name_span,
            kind,
            ..
        } => vec![symbol(
            name.clone(),
            match kind {
                ExternKind::Value(_) => SymbolKind::VARIABLE,
                ExternKind::Template(_) => SymbolKind::FUNCTION,
            },
            *span,
            *name_span,
            None,
        )],
        Stmt::Expr(_) => Vec::new(),
    }
}

fn trait_symbol(trait_def: &TraitDef) -> DocumentSymbol {
    let children = trait_def
        .methods
        .iter()
        .map(|method| {
            symbol(
                method.name.clone(),
                SymbolKind::METHOD,
                method.span,
                method.name_span,
                None,
            )
        })
        .collect();
    symbol(
        trait_def.name.clone(),
        SymbolKind::INTERFACE,
        trait_def.span,
        trait_def.name_span,
        Some(children),
    )
}

fn impl_symbol(impl_def: &ImplDef) -> DocumentSymbol {
    let children = impl_def
        .methods
        .iter()
        .map(|method| {
            symbol(
                method.name.clone(),
                SymbolKind::METHOD,
                method.span,
                method.name_span,
                None,
            )
        })
        .collect();
    symbol(
        format!("impl {}", impl_def.trait_name),
        SymbolKind::OBJECT,
        impl_def.span,
        impl_def.span,
        Some(children),
    )
}

fn inherent_impl_symbol(impl_def: &InherentImplDef) -> DocumentSymbol {
    let children = impl_def
        .methods
        .iter()
        .map(|method| {
            symbol(
                method.name.clone(),
                SymbolKind::METHOD,
                method.span,
                method.name_span,
                None,
            )
        })
        .collect();
    symbol(
        "impl".to_string(),
        SymbolKind::OBJECT,
        impl_def.span,
        impl_def.span,
        Some(children),
    )
}

fn type_symbol(type_def: &TypeDef) -> DocumentSymbol {
    let children = type_def
        .variants
        .iter()
        .map(|variant| {
            symbol(
                variant.name.clone(),
                SymbolKind::ENUM_MEMBER,
                variant.span,
                variant.name_span,
                None,
            )
        })
        .collect();
    symbol(
        type_def.name.clone(),
        SymbolKind::ENUM,
        type_def.span,
        type_def.name_span,
        Some(children),
    )
}

fn pattern_binding_symbols(pattern: &Pattern, declaration_span: SourceSpan) -> Vec<DocumentSymbol> {
    let mut bindings = Vec::new();
    collect_pattern_bindings(pattern, declaration_span, &mut bindings);
    bindings
}

fn collect_pattern_bindings(
    pattern: &Pattern,
    declaration_span: SourceSpan,
    bindings: &mut Vec<DocumentSymbol>,
) {
    match pattern {
        Pattern::Variable(name, span) => bindings.push(symbol(
            name.clone(),
            SymbolKind::VARIABLE,
            declaration_span,
            *span,
            None,
        )),
        Pattern::Constructor {
            binding: Some((name, span)),
            ..
        } => bindings.push(symbol(
            name.clone(),
            SymbolKind::VARIABLE,
            declaration_span,
            *span,
            None,
        )),
        Pattern::Record { fields, rest } => {
            for (_, name, span) in fields {
                bindings.push(symbol(
                    name.clone(),
                    SymbolKind::VARIABLE,
                    declaration_span,
                    *span,
                    None,
                ));
            }
            if let Some(Some((name, span))) = rest {
                bindings.push(symbol(
                    name.clone(),
                    SymbolKind::VARIABLE,
                    declaration_span,
                    *span,
                    None,
                ));
            }
        }
        Pattern::List { elements, rest } => {
            for element in elements {
                collect_pattern_bindings(element, declaration_span, bindings);
            }
            if let Some(Some((name, span))) = rest {
                bindings.push(symbol(
                    name.clone(),
                    SymbolKind::VARIABLE,
                    declaration_span,
                    *span,
                    None,
                ));
            }
        }
        Pattern::Tuple(elements) => {
            for element in elements {
                collect_pattern_bindings(element, declaration_span, bindings);
            }
        }
        Pattern::Wildcard | Pattern::StringLit(_) | Pattern::Constructor { binding: None, .. } => {}
    }
}

fn symbol(
    name: String,
    kind: SymbolKind,
    range: SourceSpan,
    selection_range: SourceSpan,
    children: Option<Vec<DocumentSymbol>>,
) -> DocumentSymbol {
    #[allow(deprecated)]
    DocumentSymbol {
        name,
        detail: None,
        kind,
        tags: None,
        deprecated: None,
        range: source_span_to_range(range),
        selection_range: source_span_to_range(selection_range),
        children,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::analysis::tests::TestProject;
    use lsp_types::Position;

    #[test]
    fn document_symbols_include_top_level_and_nested_items() {
        let project = TestProject::new("document-symbols");
        let source = r#"
type Option('a) = Some('a) | None
trait Show 'a {
    fn show(x: 'a) -> string
}
impl Show for f64 {
    fn show(x) { "number" }
}
fn main() { 1 }
"#;
        let (state, uri) = project.open("main.hern", source);

        let Some(DocumentSymbolResponse::Nested(symbols)) = document_symbols(&state, uri) else {
            panic!("document symbols should be available");
        };

        let option = symbols
            .iter()
            .find(|symbol| symbol.name == "Option")
            .expect("type symbol should exist");
        assert_eq!(option.kind, SymbolKind::ENUM);
        assert!(
            option
                .children
                .as_ref()
                .is_some_and(|children| children.iter().any(|symbol| symbol.name == "Some"))
        );
        let show_trait = symbols
            .iter()
            .find(|symbol| symbol.name == "Show")
            .expect("trait symbol should exist");
        assert_eq!(show_trait.kind, SymbolKind::INTERFACE);
        assert!(
            show_trait
                .children
                .as_ref()
                .is_some_and(|children| children.iter().any(|symbol| symbol.name == "show"))
        );
        assert!(symbols.iter().any(|symbol| symbol.name == "main"));
    }

    #[test]
    fn document_symbol_selection_range_targets_identifier() {
        let project = TestProject::new("document-symbol-selection");
        let (state, uri) = project.open("main.hern", "fn answer() { 42 }\n");

        let Some(DocumentSymbolResponse::Nested(symbols)) = document_symbols(&state, uri) else {
            panic!("document symbols should be available");
        };

        let answer = symbols
            .iter()
            .find(|symbol| symbol.name == "answer")
            .expect("function symbol should exist");
        assert_eq!(answer.selection_range.start, Position::new(0, 3));
        assert_eq!(answer.selection_range.end, Position::new(0, 9));
    }

    #[test]
    fn document_symbols_survive_recoverable_parse_errors() {
        let project = TestProject::new("document-symbol-recovery");
        let source = "fn before() { 1 }\nlet broken = ;\nfn after() { 2 }\n";
        let (state, uri) = project.open("main.hern", source);

        let Some(DocumentSymbolResponse::Nested(symbols)) = document_symbols(&state, uri) else {
            panic!("document symbols should be available");
        };
        let names: Vec<_> = symbols.iter().map(|symbol| symbol.name.as_str()).collect();

        assert!(names.contains(&"before"), "{names:?}");
        assert!(names.contains(&"after"), "{names:?}");
    }
}
