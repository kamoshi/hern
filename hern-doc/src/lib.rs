//! Small documentation-oriented API for analyzing Hern snippets.
//!
//! This crate intentionally exposes byte ranges and plain strings rather than
//! LSP types. Static site generators can merge these ranges with syntax
//! highlighting output without running an editor protocol server.

use hern_core::analysis::{
    CompilerDiagnostic, PreludeAnalysis, analyze_prelude_source, analyze_source, hover_at,
    prelude_source,
};
use hern_core::ast::{
    Expr, ExprKind, Pattern, Program, SourcePosition, SourceSpan, Stmt, byte_to_source_position,
    source_position_to_byte,
};
use hern_core::source_index::{DefinitionKind, SymbolId, index_program};
use hern_core::types::{Scheme, Ty, display_ty_with_var_names, free_type_vars_in_display_order};
use std::collections::{HashMap, HashSet};

/// Reusable Hern snippet analyzer with the standard prelude loaded once.
#[derive(Debug, Clone)]
pub struct Analyzer {
    prelude: PreludeAnalysis,
}

impl Analyzer {
    /// Builds an analyzer and type-checks the standard prelude.
    pub fn new() -> Result<Self, Diagnostic> {
        Ok(Self {
            prelude: analyze_prelude_source(prelude_source())
                .map_err(|diagnostic| Diagnostic::from_compiler(prelude_source(), diagnostic))?,
        })
    }

    /// Analyzes one self-contained Hern snippet.
    pub fn analyze_snippet(&self, source: &str) -> SnippetAnalysis {
        match analyze_source(source, &self.prelude) {
            Ok(analysis) => {
                let hovers = collect_hovers(source, &analysis.program, &analysis.inference);
                let annotations = collect_annotations(source, &analysis.program, &hovers);
                SnippetAnalysis {
                    diagnostics: Vec::new(),
                    hovers,
                    annotations,
                }
            }
            Err(diagnostic) => SnippetAnalysis {
                diagnostics: vec![Diagnostic::from_compiler(source, diagnostic)],
                hovers: Vec::new(),
                annotations: Vec::new(),
            },
        }
    }

    /// Starts a stateful snippet session for documentation pages.
    pub fn session(&self) -> SnippetSession<'_> {
        SnippetSession::new(self)
    }
}

/// Analyzes one self-contained snippet, constructing a fresh analyzer first.
///
/// Prefer reusing [`Analyzer`] when analyzing more than one snippet so the
/// standard prelude is parsed and inferred only once.
pub fn analyze_snippet(source: &str) -> Result<SnippetAnalysis, Diagnostic> {
    Ok(Analyzer::new()?.analyze_snippet(source))
}

/// Stateful analyzer for ordered Hern snippets on the same documentation page.
///
/// Each snippet is analyzed against the accumulated virtual source. This keeps
/// cross-snippet references and type information simple and deterministic, at
/// the cost of re-analyzing earlier snippets on every call.
#[derive(Debug)]
pub struct SnippetSession<'a> {
    analyzer: &'a Analyzer,
    source: String,
}

impl<'a> SnippetSession<'a> {
    /// Creates a session that reuses an existing analyzer.
    pub fn new(analyzer: &'a Analyzer) -> Self {
        Self {
            analyzer,
            source: String::new(),
        }
    }

    /// Analyze a snippet as a continuation of all snippets already added.
    ///
    /// The returned ranges are local to `source`, not the accumulated virtual
    /// module. This lets static site generators process Hern code fences in
    /// document order without look-ahead.
    pub fn analyze_snippet(&mut self, source: &str) -> SnippetAnalysis {
        let current_start = self.append_snippet(source);
        self.analyze_current_snippet(current_start)
    }

    /// Returns the virtual source made from all snippets seen so far.
    pub fn accumulated_source(&self) -> &str {
        &self.source
    }

    fn append_snippet(&mut self, source: &str) -> usize {
        if !self.source.is_empty() && !self.source.ends_with('\n') {
            self.source.push('\n');
        }
        let current_start = self.source.len();
        self.source.push_str(source);
        if !self.source.ends_with('\n') {
            self.source.push('\n');
        }
        current_start
    }

    fn analyze_current_snippet(&self, current_start: usize) -> SnippetAnalysis {
        let current_end = self.source.len();
        match analyze_source(&self.source, &self.analyzer.prelude) {
            Ok(analysis) => {
                let hovers = collect_hovers(&self.source, &analysis.program, &analysis.inference);
                let annotations = collect_annotations(&self.source, &analysis.program, &hovers)
                    .into_iter()
                    .filter_map(|annotation| {
                        remap_annotation(annotation, current_start, current_end)
                    })
                    .collect();
                let hovers = hovers
                    .into_iter()
                    .filter_map(|hover| remap_hover(hover, current_start, current_end))
                    .collect();
                SnippetAnalysis {
                    diagnostics: Vec::new(),
                    hovers,
                    annotations,
                }
            }
            Err(diagnostic) => {
                let diagnostic = Diagnostic::from_compiler(&self.source, diagnostic);
                SnippetAnalysis {
                    diagnostics: remap_diagnostic(diagnostic, current_start, current_end)
                        .into_iter()
                        .collect(),
                    hovers: Vec::new(),
                    annotations: Vec::new(),
                }
            }
        }
    }
}

/// Hovers and diagnostics for one snippet.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SnippetAnalysis {
    pub diagnostics: Vec<Diagnostic>,
    /// Rich semantic ranges for static HTML renderers.
    pub annotations: Vec<Annotation>,
    /// Hover-only projection kept for simple consumers.
    pub hovers: Vec<HoverAnnotation>,
}

/// Semantic information attached to a source range.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Annotation {
    /// The source range that should receive the generated HTML wrapper.
    pub range: TextRange,
    /// The broader source range that UI may choose to highlight while hovered.
    pub highlight: TextRange,
    /// Optional hover tooltip text.
    pub hover: Option<String>,
    /// Optional generated HTML id for a definition site.
    pub id: Option<String>,
    /// Optional same-page link target for a reference.
    pub link: Option<Link>,
    pub kind: AnnotationKind,
}

/// Same-page link target for a resolved Hern reference.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Link {
    pub target_id: String,
}

/// The primary semantic role of an annotation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AnnotationKind {
    Definition,
    Reference,
    Expression,
}

/// Hover text plus byte ranges for the source that should trigger and highlight it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HoverAnnotation {
    /// The source range that should display the hover tooltip.
    pub trigger: TextRange,
    /// The broader source range that UI may choose to highlight while hovered.
    pub highlight: TextRange,
    pub text: String,
}

/// Compiler diagnostic rendered with a byte range when it belongs to the snippet.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Diagnostic {
    pub range: Option<TextRange>,
    pub message: String,
}

impl Diagnostic {
    fn from_compiler(source: &str, diagnostic: CompilerDiagnostic) -> Self {
        Self {
            range: diagnostic
                .span
                .and_then(|span| TextRange::from_span(source, span)),
            message: diagnostic.message,
        }
    }
}

/// A half-open byte range in a Hern source snippet.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TextRange {
    pub start: usize,
    pub end: usize,
}

impl TextRange {
    pub fn new(start: usize, end: usize) -> Self {
        Self { start, end }
    }

    pub fn from_span(source: &str, span: SourceSpan) -> Option<Self> {
        Some(Self {
            start: source_position_to_byte(
                source,
                SourcePosition {
                    line: span.start_line,
                    col: span.start_col,
                },
            )?,
            end: source_position_to_byte(
                source,
                SourcePosition {
                    line: span.end_line,
                    col: span.end_col,
                },
            )?,
        })
    }

    fn contains(self, byte: usize) -> bool {
        byte >= self.start && byte < self.end
    }

    fn remap_from_window(self, start: usize, end: usize) -> Option<Self> {
        if self.start < start || self.end > end {
            return None;
        }
        Some(Self {
            start: self.start - start,
            end: self.end - start,
        })
    }
}

fn remap_hover(hover: HoverAnnotation, start: usize, end: usize) -> Option<HoverAnnotation> {
    Some(HoverAnnotation {
        trigger: hover.trigger.remap_from_window(start, end)?,
        highlight: hover.highlight.remap_from_window(start, end)?,
        text: hover.text,
    })
}

fn remap_annotation(
    annotation: Annotation,
    start: usize,
    end: usize,
) -> Option<Annotation> {
    Some(Annotation {
        range: annotation.range.remap_from_window(start, end)?,
        highlight: annotation.highlight.remap_from_window(start, end)?,
        hover: annotation.hover,
        id: annotation.id,
        link: annotation.link,
        kind: annotation.kind,
    })
}

fn remap_diagnostic(diagnostic: Diagnostic, start: usize, end: usize) -> Option<Diagnostic> {
    Some(Diagnostic {
        range: match diagnostic.range {
            Some(range) => Some(range.remap_from_window(start, end)?),
            None => None,
        },
        message: diagnostic.message,
    })
}

fn collect_annotations(
    source: &str,
    program: &Program,
    hovers: &[HoverAnnotation],
) -> Vec<Annotation> {
    let index = index_program(program);
    let definition_ids = definition_ids(&index);
    let mut annotations = Vec::new();

    for definition in &index.definitions {
        if !is_linkable_definition_kind(definition.kind) {
            continue;
        }
        let Some(range) = TextRange::from_span(source, definition.location.span) else {
            continue;
        };
        let Some(id) = definition_ids.get(&definition.symbol).cloned() else {
            continue;
        };
        upsert_annotation(&mut annotations, range, |annotation| {
            annotation.id = Some(id);
            annotation.kind = AnnotationKind::Definition;
        });
    }

    for reference in &index.references {
        let Some(range) = TextRange::from_span(source, reference.location.span) else {
            continue;
        };
        let Some(target_id) = definition_ids.get(&reference.symbol).cloned() else {
            continue;
        };
        upsert_annotation(&mut annotations, range, |annotation| {
            annotation.link = Some(Link { target_id });
            if annotation.kind != AnnotationKind::Definition {
                annotation.kind = AnnotationKind::Reference;
            }
        });
    }

    for hover in hovers {
        upsert_annotation(&mut annotations, hover.trigger, |annotation| {
            annotation.highlight = hover.highlight;
            annotation.hover = Some(hover.text.clone());
        });
    }

    annotations.sort_by_key(|annotation| (annotation.range.start, annotation.range.end));
    annotations
}

fn definition_ids(
    index: &hern_core::source_index::SourceIndex,
) -> HashMap<SymbolId, String> {
    let mut counts = HashMap::<String, usize>::new();
    let mut ids = HashMap::new();
    for definition in &index.definitions {
        if !is_linkable_definition_kind(definition.kind) {
            continue;
        }
        let slug = definition_slug(&definition.name);
        let count = counts.entry(slug.clone()).or_insert(0);
        *count += 1;
        let id = if *count == 1 {
            format!("hern-def-{slug}")
        } else {
            format!("hern-def-{slug}-{}", *count)
        };
        ids.insert(definition.symbol, id);
    }
    ids
}

fn is_linkable_definition_kind(kind: DefinitionKind) -> bool {
    matches!(
        kind,
        DefinitionKind::Function
            | DefinitionKind::ImplMethod
            | DefinitionKind::Let
            | DefinitionKind::Parameter
            | DefinitionKind::Trait
            | DefinitionKind::TraitMethod
            | DefinitionKind::Type
            | DefinitionKind::TypeAlias
            | DefinitionKind::Variant
            | DefinitionKind::Extern
    )
}

fn definition_slug(name: &str) -> String {
    let mut slug = String::new();
    for ch in name.chars() {
        match ch {
            'a'..='z' | 'A'..='Z' | '0'..='9' => slug.push(ch),
            '_' | '-' => slug.push('-'),
            _ => {
                if !slug.is_empty() && !slug.ends_with('-') {
                    slug.push('-');
                }
                slug.push_str(&format!("x{:x}", ch as u32));
            }
        }
    }
    let slug = slug.trim_matches('-').to_string();
    if slug.is_empty() {
        "symbol".to_string()
    } else {
        slug
    }
}

fn upsert_annotation(
    annotations: &mut Vec<Annotation>,
    range: TextRange,
    update: impl FnOnce(&mut Annotation),
) {
    if let Some(annotation) = annotations.iter_mut().find(|annotation| annotation.range == range) {
        update(annotation);
        return;
    }
    let mut annotation = Annotation {
        range,
        highlight: range,
        hover: None,
        id: None,
        link: None,
        kind: AnnotationKind::Expression,
    };
    update(&mut annotation);
    annotations.push(annotation);
}

fn collect_hovers(
    source: &str,
    program: &Program,
    inference: &hern_core::types::infer::InferenceResult,
) -> Vec<HoverAnnotation> {
    let mut hovers = Vec::new();
    let definition_schemes = &inference.definition_schemes;
    let binding_types = &inference.binding_types;
    collect_stmt_hovers(
        source,
        &program.stmts,
        definition_schemes,
        binding_types,
        &mut hovers,
    );
    collect_expr_hovers(source, program, inference, &mut hovers);
    hovers.sort_by_key(|hover| (hover.trigger.start, hover.trigger.end, hover.highlight.end));
    hovers
        .dedup_by(|a, b| a.trigger == b.trigger && a.highlight == b.highlight && a.text == b.text);
    hovers
}

fn collect_stmt_hovers(
    source: &str,
    stmts: &[Stmt],
    definition_schemes: &HashMap<SourceSpan, Scheme>,
    binding_types: &HashMap<SourceSpan, Ty>,
    hovers: &mut Vec<HoverAnnotation>,
) {
    for stmt in stmts {
        match stmt {
            Stmt::Let { pat, value, .. } => {
                collect_pattern_hovers(source, pat, definition_schemes, binding_types, hovers);
                collect_expr_stmt_hovers(source, value, definition_schemes, binding_types, hovers);
            }
            Stmt::Fn {
                span,
                name_span,
                params,
                body,
                ..
            }
            | Stmt::Op {
                span,
                name_span,
                params,
                body,
                ..
            } => {
                if let Some(scheme) = definition_schemes.get(name_span) {
                    push_hover(
                        source,
                        *name_span,
                        *name_span,
                        scheme_to_doc_string(scheme),
                        hovers,
                    );
                    if let Some(fn_span) = fn_keyword_span(source, *span, Some(*name_span)) {
                        push_hover(source, fn_span, *span, scheme_to_doc_string(scheme), hovers);
                    }
                }
                collect_param_hovers(source, params, definition_schemes, binding_types, hovers);
                collect_expr_stmt_hovers(source, body, definition_schemes, binding_types, hovers);
            }
            Stmt::Trait(trait_def) => {
                for method in &trait_def.methods {
                    let text = trait_method_signature(method);
                    push_hover(
                        source,
                        method.name_span,
                        method.name_span,
                        text.clone(),
                        hovers,
                    );
                    if let Some(fn_span) =
                        fn_keyword_span(source, method.span, Some(method.name_span))
                    {
                        push_hover(source, fn_span, method.span, text, hovers);
                    }
                }
            }
            Stmt::Impl(impl_def) => {
                for method in &impl_def.methods {
                    let text = definition_schemes
                        .get(&method.name_span)
                        .map(scheme_to_doc_string)
                        .unwrap_or_else(|| impl_method_signature(method));
                    push_hover(
                        source,
                        method.name_span,
                        method.name_span,
                        text.clone(),
                        hovers,
                    );
                    if let Some(fn_span) =
                        fn_keyword_span(source, method.span, Some(method.name_span))
                    {
                        push_hover(source, fn_span, method.span, text, hovers);
                    }
                    collect_param_hovers(
                        source,
                        &method.params,
                        definition_schemes,
                        binding_types,
                        hovers,
                    );
                    collect_expr_stmt_hovers(
                        source,
                        &method.body,
                        definition_schemes,
                        binding_types,
                        hovers,
                    );
                }
            }
            Stmt::InherentImpl(impl_def) => {
                for method in &impl_def.methods {
                    let text = definition_schemes
                        .get(&method.name_span)
                        .map(scheme_to_doc_string)
                        .unwrap_or_else(|| inherent_method_signature(method));
                    push_hover(
                        source,
                        method.name_span,
                        method.name_span,
                        text.clone(),
                        hovers,
                    );
                    if let Some(fn_span) =
                        fn_keyword_span(source, method.span, Some(method.name_span))
                    {
                        push_hover(source, fn_span, method.span, text, hovers);
                    }
                    collect_param_hovers(
                        source,
                        &method.params,
                        definition_schemes,
                        binding_types,
                        hovers,
                    );
                    collect_expr_stmt_hovers(
                        source,
                        &method.body,
                        definition_schemes,
                        binding_types,
                        hovers,
                    );
                }
            }
            Stmt::TestBlock { stmts, .. } | Stmt::RecBlock { stmts, .. } => {
                collect_stmt_hovers(source, stmts, definition_schemes, binding_types, hovers);
            }
            Stmt::Expr(expr) => {
                collect_expr_stmt_hovers(source, expr, definition_schemes, binding_types, hovers)
            }
            Stmt::Type(_) | Stmt::TypeAlias { .. } | Stmt::Extern { .. } => {}
        }
    }
}

fn collect_param_hovers(
    source: &str,
    params: &[hern_core::ast::Param],
    definition_schemes: &HashMap<SourceSpan, Scheme>,
    binding_types: &HashMap<SourceSpan, Ty>,
    hovers: &mut Vec<HoverAnnotation>,
) {
    for param in params {
        collect_pattern_hovers(source, &param.pat, definition_schemes, binding_types, hovers);
    }
}

fn collect_pattern_hovers(
    source: &str,
    pattern: &Pattern,
    definition_schemes: &HashMap<SourceSpan, Scheme>,
    binding_types: &HashMap<SourceSpan, Ty>,
    hovers: &mut Vec<HoverAnnotation>,
) {
    match pattern {
        Pattern::Variable(_, span) => {
            if let Some(scheme) = definition_schemes.get(span) {
                push_hover(source, *span, *span, scheme_to_doc_string(scheme), hovers);
            } else if let Some(ty) = binding_types.get(span) {
                push_hover(source, *span, *span, ty_to_doc_string(ty), hovers);
            }
        }
        Pattern::Constructor { binding, .. } => {
            if let Some(binding) = binding {
                collect_pattern_hovers(source, binding, definition_schemes, binding_types, hovers);
            }
        }
        Pattern::Tuple(elems) => {
            for elem in elems {
                collect_pattern_hovers(source, elem, definition_schemes, binding_types, hovers);
            }
        }
        Pattern::List { elements, rest } => {
            for elem in elements {
                collect_pattern_hovers(source, elem, definition_schemes, binding_types, hovers);
            }
            if let Some(Some((_, span))) = rest
                && let Some(scheme) = definition_schemes.get(span)
            {
                push_hover(source, *span, *span, scheme_to_doc_string(scheme), hovers);
            } else if let Some(Some((_, span))) = rest
                && let Some(ty) = binding_types.get(span)
            {
                push_hover(source, *span, *span, ty_to_doc_string(ty), hovers);
            }
        }
        Pattern::Record { fields, rest, .. } => {
            for (_, _, span) in fields {
                if let Some(scheme) = definition_schemes.get(span) {
                    push_hover(source, *span, *span, scheme_to_doc_string(scheme), hovers);
                } else if let Some(ty) = binding_types.get(span) {
                    push_hover(source, *span, *span, ty_to_doc_string(ty), hovers);
                }
            }
            if let Some(Some((_, span))) = rest
                && let Some(scheme) = definition_schemes.get(span)
            {
                push_hover(source, *span, *span, scheme_to_doc_string(scheme), hovers);
            } else if let Some(Some((_, span))) = rest
                && let Some(ty) = binding_types.get(span)
            {
                push_hover(source, *span, *span, ty_to_doc_string(ty), hovers);
            }
        }
        Pattern::Wildcard
        | Pattern::NumberLit(_)
        | Pattern::StringLit(_)
        | Pattern::BoolLit(_)
        | Pattern::IntRange { .. } => {}
    }
}

fn collect_expr_stmt_hovers(
    source: &str,
    expr: &Expr,
    definition_schemes: &HashMap<SourceSpan, Scheme>,
    binding_types: &HashMap<SourceSpan, Ty>,
    hovers: &mut Vec<HoverAnnotation>,
) {
    match &expr.kind {
        ExprKind::Lambda { params, body, .. } => {
            collect_param_hovers(source, params, definition_schemes, binding_types, hovers);
            collect_expr_stmt_hovers(source, body, definition_schemes, binding_types, hovers);
        }
        ExprKind::Grouped(inner)
        | ExprKind::Not(inner)
        | ExprKind::Neg { operand: inner, .. }
        | ExprKind::Loop(inner)
        | ExprKind::Break(Some(inner))
        | ExprKind::Return(Some(inner))
        | ExprKind::FieldAccess { expr: inner, .. } => {
            collect_expr_stmt_hovers(source, inner, definition_schemes, binding_types, hovers);
        }
        ExprKind::Assign { target, value } => {
            collect_expr_stmt_hovers(source, target, definition_schemes, binding_types, hovers);
            collect_expr_stmt_hovers(source, value, definition_schemes, binding_types, hovers);
        }
        ExprKind::Binary { lhs, rhs, .. } => {
            collect_expr_stmt_hovers(source, lhs, definition_schemes, binding_types, hovers);
            collect_expr_stmt_hovers(source, rhs, definition_schemes, binding_types, hovers);
        }
        ExprKind::Range { start, end, .. } => {
            if let Some(start) = start {
                collect_expr_stmt_hovers(source, start, definition_schemes, binding_types, hovers);
            }
            if let Some(end) = end {
                collect_expr_stmt_hovers(source, end, definition_schemes, binding_types, hovers);
            }
        }
        ExprKind::Call { callee, args, .. } => {
            collect_expr_stmt_hovers(source, callee, definition_schemes, binding_types, hovers);
            for arg in args {
                collect_expr_stmt_hovers(source, arg, definition_schemes, binding_types, hovers);
            }
        }
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
        } => {
            collect_expr_stmt_hovers(source, cond, definition_schemes, binding_types, hovers);
            collect_expr_stmt_hovers(
                source,
                then_branch,
                definition_schemes,
                binding_types,
                hovers,
            );
            collect_expr_stmt_hovers(
                source,
                else_branch,
                definition_schemes,
                binding_types,
                hovers,
            );
        }
        ExprKind::Match { scrutinee, arms } => {
            collect_expr_stmt_hovers(source, scrutinee, definition_schemes, binding_types, hovers);
            for (pattern, body) in arms {
                collect_pattern_hovers(source, pattern, definition_schemes, binding_types, hovers);
                collect_expr_stmt_hovers(source, body, definition_schemes, binding_types, hovers);
            }
        }
        ExprKind::Block { stmts, final_expr } => {
            collect_stmt_hovers(source, stmts, definition_schemes, binding_types, hovers);
            if let Some(expr) = final_expr {
                collect_expr_stmt_hovers(source, expr, definition_schemes, binding_types, hovers);
            }
        }
        ExprKind::Tuple(items) => {
            for item in items {
                collect_expr_stmt_hovers(source, item, definition_schemes, binding_types, hovers);
            }
        }
        ExprKind::Array(entries) => {
            for entry in entries {
                collect_expr_stmt_hovers(
                    source,
                    entry.expr(),
                    definition_schemes,
                    binding_types,
                    hovers,
                );
            }
        }
        ExprKind::Record(entries) => {
            for entry in entries {
                collect_expr_stmt_hovers(
                    source,
                    entry.expr(),
                    definition_schemes,
                    binding_types,
                    hovers,
                );
            }
        }
        ExprKind::Index { receiver, key, .. } => {
            collect_expr_stmt_hovers(source, receiver, definition_schemes, binding_types, hovers);
            collect_expr_stmt_hovers(source, key, definition_schemes, binding_types, hovers);
        }
        ExprKind::For {
            pat,
            iterable,
            body,
            ..
        } => {
            collect_pattern_hovers(source, pat, definition_schemes, binding_types, hovers);
            collect_expr_stmt_hovers(source, iterable, definition_schemes, binding_types, hovers);
            collect_expr_stmt_hovers(source, body, definition_schemes, binding_types, hovers);
        }
        ExprKind::Number(_)
        | ExprKind::StringLit(_)
        | ExprKind::Bool(_)
        | ExprKind::Ident(_)
        | ExprKind::Import(_)
        | ExprKind::Unit
        | ExprKind::Break(None)
        | ExprKind::Continue
        | ExprKind::Return(None)
        | ExprKind::AssociatedAccess { .. } => {}
    }
}

fn collect_expr_hovers(
    source: &str,
    program: &Program,
    inference: &hern_core::types::infer::InferenceResult,
    hovers: &mut Vec<HoverAnnotation>,
) {
    let mut seen = hovers
        .iter()
        .map(|hover| hover.trigger)
        .collect::<HashSet<_>>();
    for (byte, position) in hover_candidate_offsets(source) {
        let Some(info) = hover_at(
            program,
            &inference.expr_types,
            &inference.symbol_types,
            position,
        ) else {
            continue;
        };
        let Some(trigger) = TextRange::from_span(source, info.span) else {
            continue;
        };
        if !trigger.contains(byte) || !is_hover_token(source, trigger) || !seen.insert(trigger) {
            continue;
        }
        hovers.push(HoverAnnotation {
            trigger,
            highlight: trigger,
            text: ty_to_doc_string(&info.ty),
        });
    }
}

fn hover_candidate_offsets(source: &str) -> impl Iterator<Item = (usize, SourcePosition)> + '_ {
    let mut line = 1;
    let mut line_start = 0;
    source.char_indices().filter_map(move |(idx, ch)| {
        if ch == '\n' {
            line += 1;
            line_start = idx + ch.len_utf8();
            return None;
        }
        if ch.is_ascii_alphanumeric() || ch == '_' || ch == '"' || is_operator_char(ch) {
            Some((
                idx,
                SourcePosition {
                    line,
                    col: idx - line_start + 1,
                },
            ))
        } else {
            None
        }
    })
}

fn is_hover_token(source: &str, range: TextRange) -> bool {
    let Some(text) = source.get(range.start..range.end) else {
        return false;
    };
    let mut chars = text.chars();
    let Some(first) = chars.next() else {
        return false;
    };
    if first == '"' {
        return text.ends_with('"') && text.len() >= 2;
    }
    if first.is_ascii_digit() {
        return chars.all(|ch| ch.is_ascii_digit() || ch == '.');
    }
    if is_operator_char(first) {
        return chars.all(is_operator_char);
    }
    (first.is_ascii_alphabetic() || first == '_')
        && chars.all(|ch| ch.is_ascii_alphanumeric() || ch == '_')
}

fn is_operator_char(ch: char) -> bool {
    matches!(
        ch,
        '+' | '-'
            | '*'
            | '!'
            | '&'
            | '|'
            | '.'
            | '<'
            | '>'
            | '~'
            | '@'
            | '?'
            | '$'
            | '^'
            | '/'
            | '%'
            | '='
    )
}

fn push_hover(
    source: &str,
    trigger: SourceSpan,
    highlight: SourceSpan,
    text: String,
    hovers: &mut Vec<HoverAnnotation>,
) {
    let Some(trigger) = TextRange::from_span(source, trigger) else {
        return;
    };
    let Some(highlight) = TextRange::from_span(source, highlight) else {
        return;
    };
    hovers.push(HoverAnnotation {
        trigger,
        highlight,
        text,
    });
}

fn ty_to_doc_string(ty: &Ty) -> String {
    let vars = free_type_vars_in_display_order(ty);
    let names = vars
        .into_iter()
        .enumerate()
        .map(|(idx, var)| (var, hern_core::types::type_var_name(idx)))
        .collect();
    display_ty_with_var_names(ty, &names)
}

fn scheme_to_doc_string(scheme: &Scheme) -> String {
    ty_to_doc_string(&scheme.ty)
}

fn trait_method_signature(method: &hern_core::ast::TraitMethod) -> String {
    let params = method
        .params
        .iter()
        .map(|(_, ty)| ast_type_to_string(ty))
        .collect::<Vec<_>>()
        .join(", ");
    format!("fn({}) -> {}", params, ast_type_to_string(&method.ret_type))
}

fn impl_method_signature(method: &hern_core::ast::ImplMethod) -> String {
    let params = method
        .params
        .iter()
        .map(|param| param_signature(param))
        .collect::<Vec<_>>()
        .join(", ");
    let ret = method
        .ret_type
        .as_ref()
        .map(|ret| ast_type_to_string(&ret.ty))
        .unwrap_or_else(|| "()".to_string());
    format!("fn({params}) -> {ret}")
}

fn inherent_method_signature(method: &hern_core::ast::InherentMethod) -> String {
    let params = method
        .params
        .iter()
        .map(|param| param_signature(param))
        .collect::<Vec<_>>()
        .join(", ");
    let ret = method
        .ret_type
        .as_ref()
        .map(|ret| ast_type_to_string(&ret.ty))
        .unwrap_or_else(|| "()".to_string());
    format!("fn({params}) -> {ret}")
}

fn param_signature(param: &hern_core::ast::Param) -> String {
    param
        .ty
        .as_ref()
        .map(ast_type_to_string)
        .unwrap_or_else(|| "_".to_string())
}

fn ast_type_to_string(ty: &hern_core::ast::Type) -> String {
    use hern_core::ast::Type;
    match ty {
        Type::Ident(name) => name.clone(),
        Type::Var(name) => name.clone(),
        Type::Tuple(items) => {
            let items = items
                .iter()
                .map(ast_type_to_string)
                .collect::<Vec<_>>()
                .join(", ");
            format!("({items})")
        }
        Type::Func(params, ret) => {
            let params = params
                .iter()
                .map(type_param_to_string)
                .collect::<Vec<_>>()
                .join(", ");
            format!("fn({params}) -> {}", type_return_to_string(ret))
        }
        Type::App(con, args) => {
            let args = args
                .iter()
                .map(ast_type_to_string)
                .collect::<Vec<_>>()
                .join(", ");
            format!("{}({args})", ast_type_to_string(con))
        }
        Type::Record(fields, rest) => {
            let mut parts = fields
                .iter()
                .map(|(name, ty)| format!("{name}: {}", ast_type_to_string(ty)))
                .collect::<Vec<_>>();
            if *rest {
                parts.push("..".to_string());
            }
            format!("#{{ {} }}", parts.join(", "))
        }
        Type::Unit => "()".to_string(),
        Type::Never => "!".to_string(),
        Type::Hole => "*".to_string(),
    }
}

fn type_param_to_string(param: &hern_core::ast::TypeParam) -> String {
    let ty = ast_type_to_string(&param.ty);
    if param.mut_place {
        format!("mut {ty}")
    } else {
        ty
    }
}

fn type_return_to_string(ret: &hern_core::ast::TypeReturn) -> String {
    let ty = ast_type_to_string(&ret.ty);
    if ret.mut_place {
        format!("mut {ty}")
    } else {
        ty
    }
}

fn fn_keyword_span(
    source: &str,
    callable_span: SourceSpan,
    before_span: Option<SourceSpan>,
) -> Option<SourceSpan> {
    let start = source_position_to_byte(
        source,
        SourcePosition {
            line: callable_span.start_line,
            col: callable_span.start_col,
        },
    )?;
    let end = before_span
        .and_then(|span| {
            source_position_to_byte(
                source,
                SourcePosition {
                    line: span.start_line,
                    col: span.start_col,
                },
            )
        })
        .or_else(|| {
            source_position_to_byte(
                source,
                SourcePosition {
                    line: callable_span.end_line,
                    col: callable_span.end_col,
                },
            )
        })?;
    let relative = find_keyword(source.get(start..end)?, "fn")?;
    let keyword_start = start + relative;
    let keyword_end = keyword_start + "fn".len();
    Some(SourceSpan {
        start_line: byte_to_source_position(source, keyword_start)?.line,
        start_col: byte_to_source_position(source, keyword_start)?.col,
        end_line: byte_to_source_position(source, keyword_end)?.line,
        end_col: byte_to_source_position(source, keyword_end)?.col,
    })
}

fn find_keyword(source: &str, keyword: &str) -> Option<usize> {
    let mut offset = 0;
    while let Some(relative) = source[offset..].find(keyword) {
        let start = offset + relative;
        let end = start + keyword.len();
        let before = source[..start].chars().next_back();
        let after = source[end..].chars().next();
        if !before.is_some_and(is_identifier_char) && !after.is_some_and(is_identifier_char) {
            return Some(start);
        }
        offset = end;
    }
    None
}

fn is_identifier_char(ch: char) -> bool {
    ch.is_ascii_alphanumeric() || ch == '_'
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn analyzes_function_name_and_fn_keyword_hovers() {
        let source = "fn a(x) { x }\n";
        let analysis = analyze_snippet(source).expect("prelude should analyze");

        assert!(analysis.diagnostics.is_empty());
        assert_hover(&analysis, source, "fn", "fn('a) -> 'a");
        assert_hover(&analysis, source, "a", "fn('a) -> 'a");
        assert_hover_with_highlight(
            &analysis,
            source,
            "fn",
            "fn('a) -> 'a",
            TextRange::new(0, source.trim_end().len()),
        );
    }

    #[test]
    fn reports_source_diagnostic_without_panicking() {
        let analysis = analyze_snippet("let x: bool = 1;\n").expect("prelude should analyze");

        assert_eq!(analysis.hovers, Vec::new());
        assert_eq!(analysis.diagnostics.len(), 1);
        assert!(!analysis.diagnostics[0].message.is_empty());
    }

    #[test]
    fn session_analyzes_later_snippet_with_previous_definitions() {
        let analyzer = Analyzer::new().expect("prelude should analyze");
        let mut session = analyzer.session();

        let first = session.analyze_snippet("fn inc(x: int) -> int { x + 1 }\n");
        let second_source = "let y = inc(41);\n";
        let second = session.analyze_snippet(second_source);

        assert!(first.diagnostics.is_empty());
        assert!(second.diagnostics.is_empty());
        assert_hover(&second, second_source, "inc", "fn(int) -> int");
        assert_hover(&second, second_source, "y", "int");
    }

    #[test]
    fn session_returns_diagnostics_in_current_snippet_coordinates() {
        let analyzer = Analyzer::new().expect("prelude should analyze");
        let mut session = analyzer.session();

        let first = session.analyze_snippet("fn ok(x: int) -> int { x }\n");
        let second = session.analyze_snippet("let bad: bool = ok(1);\n");

        assert!(first.diagnostics.is_empty());
        assert_eq!(second.diagnostics.len(), 1);
        assert!(second.diagnostics[0].range.is_some());
    }

    #[test]
    fn free_function_matches_reused_analyzer_for_single_snippet() {
        let source = "fn id(x) { x }\n";
        let free = analyze_snippet(source).expect("prelude should analyze");
        let analyzer = Analyzer::new().expect("prelude should analyze");
        let reused = analyzer.analyze_snippet(source);

        assert_eq!(free, reused);
    }

    #[test]
    fn analyzes_operator_trait_impl_and_inherent_method_hovers() {
        let source = "\
fn infixl 5 |++(a: int, b: int) -> int { a - b }

trait Double 'a {
  fn double(x: 'a) -> 'a
}

impl Double for int {
  fn double(x) { x + x }
}

type Boxed = Boxed(int)

impl Boxed {
  fn value(self) -> int {
    match self { Boxed(v) -> v }
  }
}
";
        let analysis = analyze_snippet(source).expect("prelude should analyze");

        assert!(analysis.diagnostics.is_empty());
        assert_hover(&analysis, source, "|++", "fn(int, int) -> int");
        assert_hover(&analysis, source, "double", "fn('a) -> 'a");
        assert_hover_at_occurrence(&analysis, source, "double", 1, "fn(int) -> int");
        assert_hover(&analysis, source, "value", "fn(Boxed) -> int");
    }

    #[test]
    fn analyzes_list_and_record_rest_pattern_hovers() {
        let source = "\
let item = match [1, 2, 3] { [head, ..tail] -> head, [] -> 0 };
let #{ x: first, ..rest } = #{ x: 1, y: 2, z: 3 };
";
        let analysis = analyze_snippet(source).expect("prelude should analyze");

        assert!(analysis.diagnostics.is_empty());
        assert_hover(&analysis, source, "head", "int");
        assert_hover(&analysis, source, "tail", "[int]");
        assert_hover(&analysis, source, "first", "int");
        assert!(
            analysis.hovers.iter().any(|hover| {
                source[hover.trigger.start..hover.trigger.end] == *"rest"
                    && hover.text.contains("y: int")
                    && hover.text.contains("z: int")
            }),
            "missing record rest hover; hovers were {:#?}",
            analysis.hovers
        );
    }

    #[test]
    fn expression_hovers_do_not_cover_whole_calls_or_blocks() {
        let source = "\
type Nat = Z | S(Nat)

fn succ(n: Nat) -> Nat {
  S(n)
}

fn add(lhs: Nat, rhs: Nat) -> Nat {
  match lhs {
    Z -> rhs,
    S(rest) -> succ(add(rest, rhs)),
  }
}
";
        let analysis = analyze_snippet(source).expect("prelude should analyze");

        assert!(analysis.diagnostics.is_empty());
        assert_hover(&analysis, source, "succ", "fn(Nat) -> Nat");
        assert_hover(&analysis, source, "add", "fn(Nat, Nat) -> Nat");
        assert_hover_at_occurrence(&analysis, source, "succ", 1, "fn(Nat) -> Nat");
        assert_hover_at_occurrence(&analysis, source, "add", 1, "fn(Nat, Nat) -> Nat");
        assert!(
            analysis.hovers.iter().all(|hover| {
                is_hover_token(source, hover.trigger)
                    || source[hover.trigger.start..hover.trigger.end] == *"fn"
            }),
            "non-token hover leaked into docs output: {:#?}",
            analysis.hovers
        );
    }

    #[test]
    fn analyzes_function_and_lambda_parameter_hovers() {
        let source = "\
fn add_one(x: int) -> int {
  x + 1
}

let f = fn(y: string) { y };
";
        let analysis = analyze_snippet(source).expect("prelude should analyze");

        assert!(analysis.diagnostics.is_empty());
        assert_hover(&analysis, source, "x", "int");
        assert_hover(&analysis, source, "y", "string");
    }

    #[test]
    fn analyzes_number_and_do_bind_expression_hovers() {
        let source = "\
fn half_if_even(n: int) -> Option(int) {
  if n % 2 == 0 { Some(n / 2) } else { None }
}

let result = do {
  let a <- half_if_even(8);
  let b <- half_if_even(a);
  Some(a + b)
};
";
        let analysis = analyze_snippet(source).expect("prelude should analyze");

        assert!(analysis.diagnostics.is_empty());
        assert_hover(&analysis, source, "8", "int");
        assert_hover_at_occurrence(&analysis, source, "half_if_even", 1, "fn(int) -> Option(int)");
        assert_hover_at_occurrence(&analysis, source, "half_if_even", 2, "fn(int) -> Option(int)");
        assert_hover_inside(&analysis, source, "half_if_even(a)", "a", "int");
        assert_hover_inside(&analysis, source, "a + b", "+", "fn(int, int) -> int");
        assert_hover_inside(&analysis, source, "a + b", "b", "int");
        assert_hover_inside(
            &analysis,
            source,
            "let a <- half_if_even(8);",
            "<-",
            "fn(Option(int), fn(int) -> Option(int)) -> Option(int)",
        );
    }

    #[test]
    fn annotates_definitions_and_references_with_links() {
        let source = "\
fn inc(x: int) -> int { x + 1 }
let y = inc(41);
";
        let analysis = analyze_snippet(source).expect("prelude should analyze");

        assert!(analysis.diagnostics.is_empty());
        let target_id = assert_definition_id(&analysis, source, "inc");
        assert_reference_link(&analysis, source, "inc(41)", "inc", &target_id);
        assert_hover(&analysis, source, "inc", "fn(int) -> int");
    }

    #[test]
    fn annotation_links_respect_shadowing() {
        let source = "\
let value = 1;
let result = {
  let value = 2;
  value
};
";
        let analysis = analyze_snippet(source).expect("prelude should analyze");

        assert!(analysis.diagnostics.is_empty());
        let inner_id = assert_definition_id_inside(&analysis, source, "let value = 2", "value");
        assert_reference_link(&analysis, source, "  value", "value", &inner_id);
    }

    #[test]
    fn session_reference_links_to_previous_snippet_definition() {
        let analyzer = Analyzer::new().expect("prelude should analyze");
        let mut session = analyzer.session();

        let first_source = "fn inc(x: int) -> int { x + 1 }\n";
        let second_source = "let y = inc(41);\n";
        let first = session.analyze_snippet(first_source);
        let second = session.analyze_snippet(second_source);

        assert!(first.diagnostics.is_empty());
        assert!(second.diagnostics.is_empty());
        let target_id = assert_definition_id(&first, first_source, "inc");
        assert_reference_link(&second, second_source, "inc(41)", "inc", &target_id);
        assert!(
            second
                .annotations
                .iter()
                .all(|annotation| annotation.id.as_deref() != Some(target_id.as_str())),
            "later snippet should link to earlier id without redefining it locally"
        );
    }

    fn assert_hover(analysis: &SnippetAnalysis, source: &str, needle: &str, text: &str) {
        assert_hover_at_occurrence(analysis, source, needle, 0, text);
    }

    fn assert_hover_at_occurrence(
        analysis: &SnippetAnalysis,
        source: &str,
        needle: &str,
        occurrence: usize,
        text: &str,
    ) {
        let start = find_occurrence(source, needle, occurrence);
        let end = start + needle.len();
        assert!(
            analysis
                .hovers
                .iter()
                .any(|hover| hover.trigger == TextRange::new(start, end) && hover.text == text),
            "missing hover for {needle:?}; hovers were {:#?}",
            analysis.hovers
        );
    }

    fn assert_hover_with_highlight(
        analysis: &SnippetAnalysis,
        source: &str,
        needle: &str,
        text: &str,
        highlight: TextRange,
    ) {
        let start = source.find(needle).expect("needle should exist");
        let end = start + needle.len();
        assert!(
            analysis
                .hovers
                .iter()
                .any(|hover| hover.trigger == TextRange::new(start, end)
                    && hover.highlight == highlight
                    && hover.text == text),
            "missing hover for {needle:?}; hovers were {:#?}",
            analysis.hovers
        );
    }

    fn assert_hover_inside(
        analysis: &SnippetAnalysis,
        source: &str,
        context: &str,
        needle: &str,
        text: &str,
    ) {
        let context_start = source.find(context).expect("context should exist");
        let needle_start = context_start
            + source[context_start..]
                .get(..context.len())
                .and_then(|text| text.rfind(needle))
                .expect("needle should exist inside context");
        let needle_end = needle_start + needle.len();
        assert!(
            analysis.hovers.iter().any(|hover| {
                hover.trigger == TextRange::new(needle_start, needle_end) && hover.text == text
            }),
            "missing hover for {needle:?} in {context:?}; hovers were {:#?}",
            analysis.hovers
        );
    }

    fn assert_definition_id(analysis: &SnippetAnalysis, source: &str, needle: &str) -> String {
        let start = source.find(needle).expect("needle should exist");
        let end = start + needle.len();
        assert_definition_id_at(analysis, TextRange::new(start, end))
    }

    fn assert_definition_id_inside(
        analysis: &SnippetAnalysis,
        source: &str,
        context: &str,
        needle: &str,
    ) -> String {
        let context_start = source.find(context).expect("context should exist");
        let start = context_start
            + source[context_start..]
                .get(..context.len())
                .and_then(|text| text.find(needle))
                .expect("needle should exist inside context");
        assert_definition_id_at(analysis, TextRange::new(start, start + needle.len()))
    }

    fn assert_definition_id_at(analysis: &SnippetAnalysis, range: TextRange) -> String {
        analysis
            .annotations
            .iter()
            .find(|annotation| annotation.range == range)
            .and_then(|annotation| annotation.id.clone())
            .unwrap_or_else(|| {
                panic!(
                    "missing definition id at {:?}; annotations were {:#?}",
                    range, analysis.annotations
                )
            })
    }

    fn assert_reference_link(
        analysis: &SnippetAnalysis,
        source: &str,
        context: &str,
        needle: &str,
        target_id: &str,
    ) {
        let context_start = source.find(context).expect("context should exist");
        let start = context_start
            + source[context_start..]
                .get(..context.len())
                .and_then(|text| text.find(needle))
                .expect("needle should exist inside context");
        let range = TextRange::new(start, start + needle.len());
        assert!(
            analysis.annotations.iter().any(|annotation| {
                annotation.range == range
                    && annotation
                        .link
                        .as_ref()
                        .is_some_and(|link| link.target_id == target_id)
            }),
            "missing reference link at {:?}; annotations were {:#?}",
            range,
            analysis.annotations
        );
    }

    fn find_occurrence(source: &str, needle: &str, occurrence: usize) -> usize {
        let mut offset = 0;
        for _ in 0..occurrence {
            let found = source[offset..].find(needle).expect("needle should exist");
            offset += found + needle.len();
        }
        offset + source[offset..].find(needle).expect("needle should exist")
    }
}
