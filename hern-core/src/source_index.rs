use crate::ast::{Expr, ExprKind, Pattern, Program, SourcePosition, SourceSpan, Stmt};
use std::collections::HashMap;

// Used only to sort spans by approximate source size; source lines should never approach this width.
const MAX_REASONABLE_SOURCE_COLUMNS: usize = 100_000;

/// Sentinel `visibility_end` assigned to top-level definitions.
/// Top-level names are visible throughout the entire file (Hern supports mutual recursion).
const TOP_LEVEL_SCOPE_END: SourcePosition = SourcePosition {
    line: usize::MAX,
    col: usize::MAX,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct SymbolId(pub usize);

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SourceLocation {
    pub span: SourceSpan,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DefinitionKind {
    Function,
    ImplMethod,
    Let,
    Parameter,
    Trait,
    TraitMethod,
    Type,
    TypeAlias,
    Variant,
    Extern,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Definition {
    pub symbol: SymbolId,
    pub name: String,
    pub location: SourceLocation,
    pub kind: DefinitionKind,
    pub import_module: Option<String>,
    /// The earliest cursor position at which this name becomes visible in completion.
    /// For local `let` bindings this is the end of the initializer expression,
    /// so the binding is not suggested inside its own initializer.
    /// For function/lambda parameters this is the start of the body.
    /// For all other definition kinds it equals the start of `location.span`.
    pub visibility_start: SourcePosition,
    /// One-past-the-end position beyond which this name is no longer in scope.
    /// Set to `TOP_LEVEL_SCOPE_END` for top-level definitions, which are visible
    /// throughout the entire file.
    pub visibility_end: SourcePosition,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Reference {
    pub symbol: SymbolId,
    pub name: String,
    pub location: SourceLocation,
}

#[derive(Debug, Clone, Default)]
pub struct SourceIndex {
    pub definitions: Vec<Definition>,
    pub references: Vec<Reference>,
    pub import_member_references: Vec<ImportMemberReference>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ImportMemberReference {
    pub import_symbol: SymbolId,
    pub module_name: String,
    pub member_name: String,
    pub location: SourceLocation,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CompletionCandidateKind {
    /// A block-local `let` binding or pattern variable.
    Local,
    /// A `fn` or lambda parameter.
    Parameter,
    /// A top-level `fn` or `op` definition.
    Function,
    /// A top-level `let x = import "..."` binding.
    ImportBinding,
    /// A top-level `let` or `extern` that is not an import.
    TopLevel,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CompletionCandidate {
    pub name: String,
    pub kind: CompletionCandidateKind,
}

impl SourceIndex {
    pub fn definition_for_reference_at(&self, pos: SourcePosition) -> Option<&Definition> {
        let reference = self
            .references
            .iter()
            .filter(|reference| contains(reference.location.span, pos))
            .min_by_key(|reference| span_len(reference.location.span))?;
        self.definitions
            .iter()
            .find(|definition| definition.symbol == reference.symbol)
    }

    pub fn definition_at(&self, pos: SourcePosition) -> Option<&Definition> {
        self.definitions
            .iter()
            .filter(|definition| contains(definition.location.span, pos))
            .min_by_key(|definition| span_len(definition.location.span))
    }

    pub fn import_member_reference_at(
        &self,
        pos: SourcePosition,
    ) -> Option<&ImportMemberReference> {
        self.import_member_references
            .iter()
            .filter(|reference| contains(reference.location.span, pos))
            .min_by_key(|reference| span_len(reference.location.span))
    }

    pub fn definition_named(&self, name: &str) -> Option<&Definition> {
        self.definitions
            .iter()
            .find(|definition| definition.name == name)
    }

    /// Returns all source spans that refer to the same binding as the symbol at `position`.
    ///
    /// The cursor may be on either the definition name or any reference use. When
    /// `include_declaration` is true the definition's name span is included in the result.
    /// Returns an empty vec if `position` does not land on a known symbol.
    ///
    /// Results are sorted in source order (line, then column).
    pub fn references_for_symbol_at(
        &self,
        position: SourcePosition,
        include_declaration: bool,
    ) -> Vec<SourceSpan> {
        let symbol = self
            .references
            .iter()
            .filter(|r| contains(r.location.span, position))
            .min_by_key(|r| span_len(r.location.span))
            .map(|r| r.symbol)
            .or_else(|| {
                self.definitions
                    .iter()
                    .filter(|d| contains(d.location.span, position))
                    .min_by_key(|d| span_len(d.location.span))
                    .map(|d| d.symbol)
            });

        let Some(symbol) = symbol else {
            return Vec::new();
        };

        let mut spans = Vec::new();

        if include_declaration
            && let Some(def) = self.definitions.iter().find(|d| d.symbol == symbol)
        {
            spans.push(def.location.span);
        }

        for r in &self.references {
            if r.symbol == symbol {
                spans.push(r.location.span);
            }
        }

        spans.sort_by_key(|s| (s.start_line, s.start_col));
        spans.dedup();
        spans
    }

    /// Returns all spans in this index where an imported member of `module_name` named
    /// `member_name` is referenced (e.g. `dep.value`).
    pub fn import_member_references_for(
        &self,
        module_name: &str,
        member_name: &str,
    ) -> Vec<SourceSpan> {
        self.import_member_references
            .iter()
            .filter(|r| r.module_name == module_name && r.member_name == member_name)
            .map(|r| r.location.span)
            .collect()
    }

    /// Returns all names visible (in scope) at `position`, with inner-scope bindings
    /// shadowing outer-scope ones of the same name.
    ///
    /// Top-level definitions (functions, top-level lets, externs) are visible throughout
    /// the entire file, consistent with Hern's support for mutual recursion.
    ///
    /// Results are sorted alphabetically by name for deterministic output.
    pub fn visible_names_at(&self, position: SourcePosition) -> Vec<CompletionCandidate> {
        let mut visible: HashMap<String, &Definition> = HashMap::new();

        for def in &self.definitions {
            let included = matches!(
                def.kind,
                DefinitionKind::Function
                    | DefinitionKind::Let
                    | DefinitionKind::Parameter
                    | DefinitionKind::Extern
            );
            if !included {
                continue;
            }

            let is_top_level = def.visibility_end == TOP_LEVEL_SCOPE_END;
            if is_top_level {
                // Top-level names are visible throughout the file; Hern supports mutual recursion.
                visible.insert(def.name.clone(), def);
            } else {
                let def_start = (def.visibility_start.line, def.visibility_start.col);
                let def_end = (def.visibility_end.line, def.visibility_end.col);
                let cursor = (position.line, position.col);
                if cursor >= def_start && cursor < def_end {
                    visible.insert(def.name.clone(), def);
                }
            }
        }

        let mut candidates: Vec<CompletionCandidate> = visible
            .into_values()
            .map(|def| {
                let is_top_level = def.visibility_end == TOP_LEVEL_SCOPE_END;
                let kind = match def.kind {
                    DefinitionKind::Function => CompletionCandidateKind::Function,
                    DefinitionKind::Parameter => CompletionCandidateKind::Parameter,
                    DefinitionKind::Let if def.import_module.is_some() => {
                        CompletionCandidateKind::ImportBinding
                    }
                    DefinitionKind::Let if is_top_level => CompletionCandidateKind::TopLevel,
                    DefinitionKind::Let => CompletionCandidateKind::Local,
                    DefinitionKind::Extern => CompletionCandidateKind::TopLevel,
                    _ => unreachable!("non-completion kinds already filtered"),
                };
                CompletionCandidate {
                    name: def.name.clone(),
                    kind,
                }
            })
            .collect();

        candidates.sort_by(|a, b| a.name.cmp(&b.name));
        candidates
    }
}

#[derive(Debug)]
struct Scope {
    names: HashMap<String, SymbolId>,
    end: SourcePosition,
}

impl Scope {
    fn top_level() -> Self {
        Self {
            names: HashMap::new(),
            end: TOP_LEVEL_SCOPE_END,
        }
    }

    fn with_end(end: SourcePosition) -> Self {
        Self {
            names: HashMap::new(),
            end,
        }
    }
}

#[derive(Debug, Default)]
struct IndexBuilder {
    index: SourceIndex,
    scopes: Vec<Scope>,
}

pub fn index_program(program: &Program) -> SourceIndex {
    let mut builder = IndexBuilder::default();
    builder.push_top_scope();

    for stmt in &program.stmts {
        builder.define_top_level(stmt);
    }
    for stmt in &program.stmts {
        builder.index_top_level_stmt(stmt);
    }

    builder.index
}

impl IndexBuilder {
    fn push_top_scope(&mut self) {
        self.scopes.push(Scope::top_level());
    }

    fn push_scope_with_end(&mut self, end: SourcePosition) {
        self.scopes.push(Scope::with_end(end));
    }

    fn pop_scope(&mut self) {
        self.scopes.pop();
    }

    fn define(&mut self, name: &str, span: SourceSpan, kind: DefinitionKind) -> SymbolId {
        let start = SourcePosition {
            line: span.start_line,
            col: span.start_col,
        };
        self.define_core(name, span, kind, None, start)
    }

    fn define_with_import(
        &mut self,
        name: &str,
        span: SourceSpan,
        kind: DefinitionKind,
        import_module: Option<String>,
    ) -> SymbolId {
        let start = SourcePosition {
            line: span.start_line,
            col: span.start_col,
        };
        self.define_core(name, span, kind, import_module, start)
    }

    /// Core define that accepts an explicit `visibility_start`.
    ///
    /// Use `define` or `define_with_import` for the common case where visibility starts at the
    /// definition site. Call this directly when the binding should only become visible later —
    /// for example, after a `let` initializer or at the first token of a function body.
    fn define_core(
        &mut self,
        name: &str,
        span: SourceSpan,
        kind: DefinitionKind,
        import_module: Option<String>,
        visibility_start: SourcePosition,
    ) -> SymbolId {
        let visibility_end = self
            .scopes
            .last()
            .map(|s| s.end)
            .unwrap_or(TOP_LEVEL_SCOPE_END);
        let symbol = SymbolId(self.index.definitions.len());
        self.index.definitions.push(Definition {
            symbol,
            name: name.to_string(),
            location: SourceLocation { span },
            kind,
            import_module,
            visibility_start,
            visibility_end,
        });
        // The root scope is pushed on construction and never popped, so last_mut always succeeds.
        self.scopes
            .last_mut()
            .expect("index builder should always have a scope")
            .names
            .insert(name.to_string(), symbol);
        symbol
    }

    fn definition(&self, symbol: SymbolId) -> Option<&Definition> {
        self.index
            .definitions
            .iter()
            .find(|definition| definition.symbol == symbol)
    }

    fn resolve(&self, name: &str) -> Option<SymbolId> {
        self.scopes
            .iter()
            .rev()
            .find_map(|scope| scope.names.get(name).copied())
    }

    fn reference(&mut self, name: &str, span: SourceSpan) {
        let Some(symbol) = self.resolve(name) else {
            return;
        };
        self.index.references.push(Reference {
            symbol,
            name: name.to_string(),
            location: SourceLocation { span },
        });
    }

    fn define_top_level(&mut self, stmt: &Stmt) {
        match stmt {
            Stmt::Let { pat, value, .. } => {
                self.define_let_pattern_top_level(pat, import_module_name(value));
            }
            Stmt::Fn {
                name, name_span, ..
            } => {
                self.define(name, *name_span, DefinitionKind::Function);
            }
            Stmt::Op {
                name, name_span, ..
            } => {
                self.define(name, *name_span, DefinitionKind::Function);
            }
            Stmt::Trait(trait_def) => {
                self.define(&trait_def.name, trait_def.name_span, DefinitionKind::Trait);
                for method in &trait_def.methods {
                    self.define(&method.name, method.name_span, DefinitionKind::TraitMethod);
                }
            }
            Stmt::Impl(impl_def) => {
                for method in &impl_def.methods {
                    self.define(&method.name, method.name_span, DefinitionKind::ImplMethod);
                }
            }
            Stmt::Type(type_def) => {
                self.define(&type_def.name, type_def.name_span, DefinitionKind::Type);
                for variant in &type_def.variants {
                    self.define(&variant.name, variant.name_span, DefinitionKind::Variant);
                }
            }
            Stmt::TypeAlias {
                name, name_span, ..
            } => {
                self.define(name, *name_span, DefinitionKind::TypeAlias);
            }
            Stmt::Extern {
                name, name_span, ..
            } => {
                self.define(name, *name_span, DefinitionKind::Extern);
            }
            Stmt::Expr(_) => {}
        }
    }

    fn index_top_level_stmt(&mut self, stmt: &Stmt) {
        match stmt {
            Stmt::Let { value, .. } | Stmt::Expr(value) => self.index_expr(value),
            Stmt::Fn {
                name_span,
                params,
                body,
                ..
            }
            | Stmt::Op {
                name_span,
                params,
                body,
                ..
            } => self.index_callable_body(params, *name_span, body),
            Stmt::Impl(impl_def) => {
                for method in &impl_def.methods {
                    self.index_callable_body(&method.params, method.span, &method.body);
                }
            }
            Stmt::Trait(_) | Stmt::Type(_) | Stmt::TypeAlias { .. } | Stmt::Extern { .. } => {}
        }
    }

    fn index_stmt(&mut self, stmt: &Stmt) {
        match stmt {
            Stmt::Let { pat, value, .. } => {
                self.index_expr(value);
                // Visibility starts after the initializer so the binding is not
                // suggested inside its own right-hand side expression.
                let visibility_start = SourcePosition {
                    line: value.span.end_line,
                    col: value.span.end_col,
                };
                self.define_let_pattern_local(pat, import_module_name(value), visibility_start);
            }
            Stmt::Expr(value) => self.index_expr(value),
            Stmt::Fn {
                name,
                name_span,
                params,
                body,
                ..
            }
            | Stmt::Op {
                name,
                name_span,
                params,
                body,
                ..
            } => {
                self.define(name, *name_span, DefinitionKind::Function);
                self.index_callable_body(params, *name_span, body);
            }
            Stmt::Impl(impl_def) => {
                for method in &impl_def.methods {
                    self.index_callable_body(&method.params, method.span, &method.body);
                }
            }
            Stmt::Trait(_) | Stmt::Type(_) | Stmt::TypeAlias { .. } | Stmt::Extern { .. } => {}
        }
    }

    fn index_callable_body(
        &mut self,
        params: &[(Pattern, Option<crate::ast::Type>)],
        _span: SourceSpan,
        body: &Expr,
    ) {
        let scope_end = SourcePosition {
            line: body.span.end_line,
            col: body.span.end_col,
        };
        let body_start = SourcePosition {
            line: body.span.start_line,
            col: body.span.start_col,
        };
        self.push_scope_with_end(scope_end);
        for (pat, _) in params {
            self.define_param_pattern_bindings(pat, body_start);
        }
        self.index_expr(body);
        self.pop_scope();
    }

    fn define_param_pattern_bindings(&mut self, pattern: &Pattern, visible_from: SourcePosition) {
        match pattern {
            Pattern::Variable(name, span) => {
                self.define_core(name, *span, DefinitionKind::Parameter, None, visible_from);
            }
            Pattern::Constructor {
                binding: Some((name, span)),
                ..
            } => {
                self.define_core(name, *span, DefinitionKind::Parameter, None, visible_from);
            }
            Pattern::Record { fields, rest } => {
                for (_, binding, span) in fields {
                    if binding != "_" {
                        self.define_core(
                            binding,
                            *span,
                            DefinitionKind::Parameter,
                            None,
                            visible_from,
                        );
                    }
                }
                if let Some(Some((rest_name, rest_span))) = rest {
                    self.define_core(
                        rest_name,
                        *rest_span,
                        DefinitionKind::Parameter,
                        None,
                        visible_from,
                    );
                }
            }
            Pattern::List { elements, rest } => {
                for elem in elements {
                    self.define_param_pattern_bindings(elem, visible_from);
                }
                if let Some(Some((rest_name, rest_span))) = rest {
                    self.define_core(
                        rest_name,
                        *rest_span,
                        DefinitionKind::Parameter,
                        None,
                        visible_from,
                    );
                }
            }
            Pattern::Tuple(elems) => {
                for elem in elems {
                    self.define_param_pattern_bindings(elem, visible_from);
                }
            }
            _ => {}
        }
    }

    fn index_expr(&mut self, expr: &Expr) {
        match &expr.kind {
            ExprKind::Ident(name) => self.reference(name, expr.span),
            ExprKind::Not(expr)
            | ExprKind::Loop(expr)
            | ExprKind::Break(Some(expr))
            | ExprKind::Return(Some(expr)) => self.index_expr(expr),
            ExprKind::Assign { target, value }
            | ExprKind::Binary {
                lhs: target,
                rhs: value,
                ..
            } => {
                self.index_expr(target);
                self.index_expr(value);
            }
            ExprKind::Call { callee, args, .. } => {
                self.index_expr(callee);
                for arg in args {
                    self.index_expr(arg);
                }
            }
            ExprKind::If {
                cond,
                then_branch,
                else_branch,
            } => {
                self.index_expr(cond);
                self.index_expr(then_branch);
                self.index_expr(else_branch);
            }
            ExprKind::Match { scrutinee, arms } => {
                self.index_expr(scrutinee);
                for (pattern, body) in arms {
                    let scope_end = SourcePosition {
                        line: body.span.end_line,
                        col: body.span.end_col,
                    };
                    self.push_scope_with_end(scope_end);
                    self.define_pattern_bindings(pattern);
                    self.index_expr(body);
                    self.pop_scope();
                }
            }
            ExprKind::Block { stmts, final_expr } => {
                let scope_end = SourcePosition {
                    line: expr.span.end_line,
                    col: expr.span.end_col,
                };
                self.push_scope_with_end(scope_end);
                for stmt in stmts {
                    self.index_stmt(stmt);
                }
                if let Some(expr) = final_expr {
                    self.index_expr(expr);
                }
                self.pop_scope();
            }
            ExprKind::Tuple(items) | ExprKind::Array(items) => {
                for item in items {
                    self.index_expr(item);
                }
            }
            ExprKind::Record(fields) => {
                for (_, value) in fields {
                    self.index_expr(value);
                }
            }
            ExprKind::FieldAccess {
                expr,
                field,
                field_span,
            } => {
                self.index_expr(expr);
                let target = if let ExprKind::Ident(base_name) = &expr.kind
                    && let Some(symbol) = self.resolve(base_name)
                    && let Some(module_name) = self
                        .definition(symbol)
                        .and_then(|definition| definition.import_module.as_ref())
                        .cloned()
                {
                    Some((symbol, module_name))
                } else {
                    None
                };
                if let Some((symbol, module_name)) = target {
                    self.index
                        .import_member_references
                        .push(ImportMemberReference {
                            import_symbol: symbol,
                            module_name,
                            member_name: field.clone(),
                            location: SourceLocation { span: *field_span },
                        });
                }
            }
            ExprKind::For {
                pat,
                iterable,
                body,
                ..
            } => {
                self.index_expr(iterable);
                let scope_end = SourcePosition {
                    line: body.span.end_line,
                    col: body.span.end_col,
                };
                self.push_scope_with_end(scope_end);
                self.define_pattern_bindings(pat);
                self.index_expr(body);
                self.pop_scope();
            }
            ExprKind::Lambda { params, body } => {
                let scope_end = SourcePosition {
                    line: body.span.end_line,
                    col: body.span.end_col,
                };
                let body_start = SourcePosition {
                    line: body.span.start_line,
                    col: body.span.start_col,
                };
                self.push_scope_with_end(scope_end);
                for (pat, _) in params {
                    self.define_param_pattern_bindings(pat, body_start);
                }
                self.index_expr(body);
                self.pop_scope();
            }
            ExprKind::Break(None)
            | ExprKind::Return(None)
            | ExprKind::Continue
            | ExprKind::Number(_)
            | ExprKind::StringLit(_)
            | ExprKind::Bool(_)
            | ExprKind::Import(_)
            | ExprKind::Unit => {}
        }
    }

    fn define_pattern_bindings(&mut self, pattern: &Pattern) {
        match pattern {
            Pattern::Wildcard | Pattern::StringLit(_) => {}
            Pattern::Variable(name, span) => {
                self.define(name, *span, DefinitionKind::Let);
            }
            Pattern::Constructor {
                binding: Some((name, span)),
                ..
            } => {
                self.define(name, *span, DefinitionKind::Let);
            }
            Pattern::Constructor { binding: None, .. } => {}
            Pattern::Record { fields, rest } => {
                for (_, binding, span) in fields {
                    if binding != "_" {
                        self.define(binding, *span, DefinitionKind::Let);
                    }
                }
                if let Some(Some((rest_name, rest_span))) = rest {
                    self.define(rest_name, *rest_span, DefinitionKind::Let);
                }
            }
            Pattern::List { elements, rest } => {
                for elem in elements {
                    self.define_pattern_bindings(elem);
                }
                if let Some(Some((rest_name, rest_span))) = rest {
                    self.define(rest_name, *rest_span, DefinitionKind::Let);
                }
            }
            Pattern::Tuple(elems) => {
                for elem in elems {
                    self.define_pattern_bindings(elem);
                }
            }
        }
    }

    fn define_let_pattern_top_level(&mut self, pattern: &Pattern, module_name: Option<String>) {
        match pattern {
            Pattern::Variable(name, span) => {
                self.define_with_import(name, *span, DefinitionKind::Let, module_name);
            }
            Pattern::Wildcard
            | Pattern::StringLit(_)
            | Pattern::Constructor { binding: None, .. } => {}
            Pattern::Constructor {
                binding: Some((name, span)),
                ..
            } => {
                self.define_with_import(name, *span, DefinitionKind::Let, module_name);
            }
            Pattern::Record { fields, rest } => {
                for (_, binding, span) in fields {
                    if binding != "_" {
                        self.define_with_import(
                            binding,
                            *span,
                            DefinitionKind::Let,
                            module_name.clone(),
                        );
                    }
                }
                if let Some(Some((rest_name, rest_span))) = rest {
                    self.define_with_import(
                        rest_name,
                        *rest_span,
                        DefinitionKind::Let,
                        module_name,
                    );
                }
            }
            Pattern::List { elements, rest } => {
                for elem in elements {
                    self.define_let_pattern_top_level(elem, module_name.clone());
                }
                if let Some(Some((rest_name, rest_span))) = rest {
                    self.define_with_import(
                        rest_name,
                        *rest_span,
                        DefinitionKind::Let,
                        module_name,
                    );
                }
            }
            Pattern::Tuple(elems) => {
                for elem in elems {
                    self.define_let_pattern_top_level(elem, module_name.clone());
                }
            }
        }
    }

    fn define_let_pattern_local(
        &mut self,
        pattern: &Pattern,
        module_name: Option<String>,
        visible_from: SourcePosition,
    ) {
        match pattern {
            Pattern::Variable(name, span) => {
                self.define_core(name, *span, DefinitionKind::Let, module_name, visible_from);
            }
            Pattern::Wildcard
            | Pattern::StringLit(_)
            | Pattern::Constructor { binding: None, .. } => {}
            Pattern::Constructor {
                binding: Some((name, span)),
                ..
            } => {
                self.define_core(name, *span, DefinitionKind::Let, module_name, visible_from);
            }
            Pattern::Record { fields, rest } => {
                for (_, binding, span) in fields {
                    if binding != "_" {
                        self.define_core(
                            binding,
                            *span,
                            DefinitionKind::Let,
                            module_name.clone(),
                            visible_from,
                        );
                    }
                }
                if let Some(Some((rest_name, rest_span))) = rest {
                    self.define_core(
                        rest_name,
                        *rest_span,
                        DefinitionKind::Let,
                        module_name,
                        visible_from,
                    );
                }
            }
            Pattern::List { elements, rest } => {
                for elem in elements {
                    self.define_let_pattern_local(elem, module_name.clone(), visible_from);
                }
                if let Some(Some((rest_name, rest_span))) = rest {
                    self.define_core(
                        rest_name,
                        *rest_span,
                        DefinitionKind::Let,
                        module_name,
                        visible_from,
                    );
                }
            }
            Pattern::Tuple(elems) => {
                for elem in elems {
                    self.define_let_pattern_local(elem, module_name.clone(), visible_from);
                }
            }
        }
    }
} // end impl IndexBuilder

fn import_module_name(expr: &Expr) -> Option<String> {
    if let ExprKind::Import(module_name) = &expr.kind {
        Some(module_name.clone())
    } else {
        None
    }
}

fn contains(span: SourceSpan, pos: SourcePosition) -> bool {
    if span.start_line == 0 {
        return false;
    }
    (pos.line, pos.col) >= (span.start_line, span.start_col)
        && (pos.line, pos.col) < (span.end_line, span.end_col)
}

fn span_len(span: SourceSpan) -> usize {
    let line_delta = span.end_line.saturating_sub(span.start_line);
    let col_delta = span.end_col.saturating_sub(span.start_col);
    line_delta * MAX_REASONABLE_SOURCE_COLUMNS + col_delta
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::pipeline::parse_source;

    fn definition_name_at(source: &str, line: usize, col: usize) -> Option<String> {
        let program = parse_source(source).expect("source should parse");
        let index = index_program(&program);
        index
            .definition_for_reference_at(SourcePosition { line, col })
            .map(|definition| definition.name.clone())
    }

    #[test]
    fn resolves_top_level_definition_references() {
        let source = "fn value() { 1 }\nvalue()\n";

        assert_eq!(definition_name_at(source, 2, 2), Some("value".to_string()));
    }

    #[test]
    fn resolves_local_let_references_to_nearest_binding() {
        let source = "let value = 1;\n{ let value = 2; value }\n";

        let program = parse_source(source).expect("source should parse");
        let index = index_program(&program);
        let definition = index
            .definition_for_reference_at(SourcePosition { line: 2, col: 18 })
            .expect("reference should resolve");

        assert_eq!(definition.name, "value");
        assert_eq!(definition.location.span.start_line, 2);
    }

    #[test]
    fn records_import_member_references() {
        let source = "let dep = import \"dep\";\ndep.value()\n";
        let program = parse_source(source).expect("source should parse");
        let index = index_program(&program);
        let reference = index
            .import_member_reference_at(SourcePosition { line: 2, col: 5 })
            .expect("import member reference should be recorded");

        assert_eq!(reference.module_name, "dep");
        assert_eq!(reference.member_name, "value");
        assert_eq!(reference.location.span.start_col, 5);
    }

    #[test]
    fn source_index_lookup_treats_span_end_as_exclusive() {
        let source = "fn value() { 1 }\nvalue()\n";
        let program = parse_source(source).expect("source should parse");
        let index = index_program(&program);

        assert!(
            index
                .definition_for_reference_at(SourcePosition { line: 2, col: 5 })
                .is_some()
        );
        assert!(
            index
                .definition_for_reference_at(SourcePosition { line: 2, col: 6 })
                .is_none()
        );
    }

    #[test]
    fn references_for_symbol_at_cursor_on_use_returns_use() {
        let source = "let value = 1;\nvalue\n";
        let program = parse_source(source).expect("source should parse");
        let index = index_program(&program);

        let spans = index.references_for_symbol_at(SourcePosition { line: 2, col: 1 }, false);

        assert_eq!(spans.len(), 1);
        assert_eq!(spans[0].start_line, 2);
    }

    #[test]
    fn references_for_symbol_at_include_declaration_prepends_definition() {
        let source = "let value = 1;\nvalue\n";
        let program = parse_source(source).expect("source should parse");
        let index = index_program(&program);

        let spans = index.references_for_symbol_at(SourcePosition { line: 2, col: 1 }, true);

        assert_eq!(spans.len(), 2);
        // sorted by source order: definition (line 1) before use (line 2)
        assert_eq!(spans[0].start_line, 1);
        assert_eq!(spans[1].start_line, 2);
    }

    #[test]
    fn references_for_symbol_at_cursor_on_declaration_returns_all() {
        let source = "fn value() { 1 }\nvalue()\n";
        let program = parse_source(source).expect("source should parse");
        let index = index_program(&program);

        // cursor on "value" declaration name (line 1, col 4)
        let spans = index.references_for_symbol_at(SourcePosition { line: 1, col: 4 }, true);

        assert_eq!(spans.len(), 2);
        assert_eq!(spans[0].start_line, 1); // declaration
        assert_eq!(spans[1].start_line, 2); // use
    }

    #[test]
    fn references_for_symbol_at_respects_shadowing() {
        // outer `value` (line 1) and inner `value` (line 2) are distinct bindings
        let source = "let value = 1;\n{ let value = 2; value }\n";
        let program = parse_source(source).expect("source should parse");
        let index = index_program(&program);

        // cursor on inner `value` use (line 2, col 18 — after `let value = 2; `)
        let inner_spans = index.references_for_symbol_at(SourcePosition { line: 2, col: 18 }, true);

        // exactly two spans: the inner definition and the single inner use, both on line 2
        assert_eq!(inner_spans.len(), 2);
        assert!(inner_spans.iter().all(|s| s.start_line == 2));

        // cursor on outer `value` declaration (line 1, col 5)
        let outer_spans = index.references_for_symbol_at(SourcePosition { line: 1, col: 5 }, true);

        // exactly one span: the outer declaration; it has no references (shadowed inside the block)
        assert_eq!(outer_spans.len(), 1);
        assert_eq!(outer_spans[0].start_line, 1);
    }

    #[test]
    fn references_for_symbol_at_unknown_position_returns_empty() {
        let source = "let value = 1;\n";
        let program = parse_source(source).expect("source should parse");
        let index = index_program(&program);

        let spans = index.references_for_symbol_at(SourcePosition { line: 99, col: 1 }, true);

        assert!(spans.is_empty());
    }

    #[test]
    fn references_for_symbol_at_span_end_is_exclusive() {
        let source = "fn value() { 1 }\nvalue()\n";
        let program = parse_source(source).expect("source should parse");
        let index = index_program(&program);

        // col 6 is one past the end of "value" (cols 1–5) on line 2
        let spans = index.references_for_symbol_at(SourcePosition { line: 2, col: 6 }, false);

        assert!(spans.is_empty());
    }

    #[test]
    fn import_member_references_for_returns_matching_spans() {
        let source = "let dep = import \"dep\";\ndep.value()\ndep.value\n";
        let program = parse_source(source).expect("source should parse");
        let index = index_program(&program);

        let spans = index.import_member_references_for("dep", "value");

        assert_eq!(spans.len(), 2);
    }

    #[test]
    fn import_member_references_for_filters_by_member_name() {
        let source = "let dep = import \"dep\";\ndep.value()\ndep.other\n";
        let program = parse_source(source).expect("source should parse");
        let index = index_program(&program);

        let value_spans = index.import_member_references_for("dep", "value");
        let other_spans = index.import_member_references_for("dep", "other");

        assert_eq!(value_spans.len(), 1);
        assert_eq!(other_spans.len(), 1);
    }

    #[test]
    fn visible_names_at_excludes_let_binding_from_its_own_initializer() {
        // `x` should not be suggested while typing its own initializer.
        // source: fn f() { let x = <cursor>; x }
        //                              ^--- col 21 is inside the initializer `1`
        let source = "fn f() { let x = 1; x }\n";
        let program = parse_source(source).expect("source should parse");
        let index = index_program(&program);

        // cursor at col 18, inside `let x = <here>1` (before the value)
        let candidates = index.visible_names_at(SourcePosition { line: 1, col: 18 });

        assert!(
            !candidates.iter().any(|c| c.name == "x"),
            "`x` should not be visible inside its own initializer"
        );
    }

    #[test]
    fn visible_names_at_parameters_visible_inside_body_not_before() {
        // Parameters should not appear before the function body begins.
        // source: fn add(x, y) { x }
        //                  ^--- col 8 is still in the signature
        let source = "fn add(x: Int, y: Int) { x }\n";
        let program = parse_source(source).expect("source should parse");
        let index = index_program(&program);

        // cursor inside the body (col 26 is on `x`)
        let inside = index.visible_names_at(SourcePosition { line: 1, col: 26 });
        assert!(
            inside
                .iter()
                .any(|c| c.name == "x" && c.kind == CompletionCandidateKind::Parameter),
            "`x` should be visible inside the body"
        );
        assert!(
            inside
                .iter()
                .any(|c| c.name == "y" && c.kind == CompletionCandidateKind::Parameter),
            "`y` should be visible inside the body"
        );

        // cursor in the signature, before the body opens (col 8 is on `x` in `(x`)
        let before = index.visible_names_at(SourcePosition { line: 1, col: 8 });
        assert!(
            !before.iter().any(|c| c.name == "x" || c.name == "y"),
            "parameters should not be visible in the signature"
        );
    }

    #[test]
    fn visible_names_at_returns_top_level_function_throughout_file() {
        // Top-level fn is always visible; Hern supports mutual recursion.
        let source = "fn value() { 1 }\nvalue()\n";
        let program = parse_source(source).expect("source should parse");
        let index = index_program(&program);

        let candidates = index.visible_names_at(SourcePosition { line: 2, col: 1 });

        assert!(
            candidates
                .iter()
                .any(|c| c.name == "value" && c.kind == CompletionCandidateKind::Function)
        );
    }

    #[test]
    fn visible_names_at_includes_block_local_inside_scope() {
        // `x` is a local let inside the fn body; both `x` and `outer` are visible at its use site.
        let source = "fn outer() { let x = 1; x }\n";
        let program = parse_source(source).expect("source should parse");
        let index = index_program(&program);

        // cursor on `x` inside the fn body
        let candidates = index.visible_names_at(SourcePosition { line: 1, col: 25 });

        assert!(
            candidates
                .iter()
                .any(|c| c.name == "x" && c.kind == CompletionCandidateKind::Local)
        );
        assert!(
            candidates
                .iter()
                .any(|c| c.name == "outer" && c.kind == CompletionCandidateKind::Function)
        );
    }

    #[test]
    fn visible_names_at_excludes_block_local_outside_scope() {
        // `x` is defined inside a block; after the block it is out of scope.
        let source = "let y = { let x = 1; x };\ny\n";
        let program = parse_source(source).expect("source should parse");
        let index = index_program(&program);

        // cursor on `y` at line 2 — outside the block
        let candidates = index.visible_names_at(SourcePosition { line: 2, col: 1 });

        assert!(!candidates.iter().any(|c| c.name == "x"));
        assert!(
            candidates
                .iter()
                .any(|c| c.name == "y" && c.kind == CompletionCandidateKind::TopLevel)
        );
    }

    #[test]
    fn visible_names_at_inner_binding_shadows_outer_inside_block() {
        // Inner `value` shadows outer `value` inside the block.
        let source = "let value = 1;\n{ let value = 2; value }\n";
        let program = parse_source(source).expect("source should parse");
        let index = index_program(&program);

        // cursor on inner `value` use (line 2, col 18)
        let candidates = index.visible_names_at(SourcePosition { line: 2, col: 18 });

        let matching: Vec<_> = candidates.iter().filter(|c| c.name == "value").collect();
        assert_eq!(matching.len(), 1, "exactly one `value` should be visible");
        assert_eq!(matching[0].kind, CompletionCandidateKind::Local);
    }

    #[test]
    fn visible_names_at_outer_binding_restored_after_inner_block() {
        // After the inner block ends, the outer top-level `value` is the only `value` in scope.
        let source = "let value = 1;\n{ let value = 2; };\nvalue\n";
        let program = parse_source(source).expect("source should parse");
        let index = index_program(&program);

        // cursor on `value` at line 3 — after the inner block
        let candidates = index.visible_names_at(SourcePosition { line: 3, col: 1 });

        let matching: Vec<_> = candidates.iter().filter(|c| c.name == "value").collect();
        assert_eq!(matching.len(), 1, "exactly one `value` should be visible");
        assert_eq!(matching[0].kind, CompletionCandidateKind::TopLevel);
    }
}
