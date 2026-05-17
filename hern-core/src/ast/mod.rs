use crate::lex::{NumberLiteral, error::Span};

pub type NodeId = u32;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct SourceSpan {
    pub start_line: usize,
    pub start_col: usize,
    pub end_line: usize,
    pub end_col: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SourcePosition {
    pub line: usize,
    pub col: usize,
}

impl SourceSpan {
    pub fn synthetic() -> Self {
        Self {
            start_line: 0,
            start_col: 0,
            end_line: 0,
            end_col: 0,
        }
    }

    pub fn is_synthetic(&self) -> bool {
        *self == Self::synthetic()
    }

    pub fn from_lex_span(span: Span) -> Self {
        Self {
            start_line: span.line,
            start_col: span.col,
            end_line: span.line,
            end_col: span.col + span.len,
        }
    }

    pub fn from_bounds(start: Span, end: Span) -> Self {
        Self {
            start_line: start.line,
            start_col: start.col,
            end_line: end.line,
            end_col: end.col + end.len,
        }
    }
}

/// Converts a 1-based source position to a byte offset in `source`.
///
/// Hern source columns are byte columns. This matches the lexer/parser spans
/// and keeps callers independent of LSP's UTF-16 position model.
///
/// Columns past the end of an existing line are clamped to that line's final
/// byte. This is useful for diagnostics and editor positions that point at
/// virtual end-of-line columns, but it means malformed positions do not
/// necessarily round-trip through [`byte_to_source_position`].
pub fn source_position_to_byte(source: &str, position: SourcePosition) -> Option<usize> {
    let mut line_start = 0;
    for (idx, line) in source.split_inclusive('\n').enumerate() {
        if idx + 1 == position.line {
            let line_without_newline = line.strip_suffix('\n').unwrap_or(line);
            return Some(
                line_start
                    + position
                        .col
                        .saturating_sub(1)
                        .min(line_without_newline.len()),
            );
        }
        line_start += line.len();
    }
    if position.line == source.lines().count() + 1 && position.col == 1 {
        Some(source.len())
    } else {
        None
    }
}

/// Converts a byte offset in `source` to a 1-based Hern source position.
///
/// The returned column is the natural byte column for `byte`; it is not clamped.
pub fn byte_to_source_position(source: &str, byte: usize) -> Option<SourcePosition> {
    if byte > source.len() {
        return None;
    }
    let mut line = 1;
    let mut line_start = 0;
    for (idx, ch) in source.char_indices() {
        if idx >= byte {
            break;
        }
        if ch == '\n' {
            line += 1;
            line_start = idx + ch.len_utf8();
        }
    }
    Some(SourcePosition {
        line,
        col: byte.saturating_sub(line_start) + 1,
    })
}

#[derive(Debug, Clone)]
pub struct Program {
    pub stmts: Vec<Stmt>,
    pub inner_attrs: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Attribute {
    pub name: String,
    pub args: Vec<String>,
    pub span: SourceSpan,
}

impl Attribute {
    pub fn is(&self, name: &str) -> bool {
        self.name == name
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DeriveTrait {
    Eq,
    ToString,
}

impl DeriveTrait {
    pub fn name(self) -> &'static str {
        match self {
            DeriveTrait::Eq => "Eq",
            DeriveTrait::ToString => "ToString",
        }
    }
}

#[derive(Debug, Clone)]
pub struct DeriveAttr {
    pub traits: Vec<DeriveTrait>,
    pub span: SourceSpan,
}

#[derive(Debug, Clone)]
pub enum GeneratedBy {
    Derive {
        trait_name: String,
        source_span: SourceSpan,
    },
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Fixity {
    Left,
    Right,
    Non,
}

#[derive(Debug, Clone)]
pub enum Stmt {
    Let {
        span: SourceSpan,
        pat: Pattern,
        is_mutable: bool,
        ty: Option<Type>,
        value: Expr,
    },
    Fn {
        attrs: Vec<Attribute>,
        span: SourceSpan,
        name: String,
        name_span: SourceSpan,
        params: Vec<Param>,
        ret_type: Option<TypeReturn>,
        body: Expr,
        dict_params: Vec<String>,
        type_bounds: Vec<TypeBound>,
    },
    Op {
        span: SourceSpan,
        name: String,
        name_span: SourceSpan,
        fixity: Fixity,
        prec: u8,
        params: Vec<Param>,
        ret_type: Option<TypeReturn>,
        body: Expr,
        dict_params: Vec<String>,
        type_bounds: Vec<TypeBound>,
    },
    Trait(TraitDef),
    Impl(ImplDef),
    InherentImpl(InherentImplDef),
    TestBlock {
        span: SourceSpan,
        stmts: Vec<Stmt>,
    },
    RecBlock {
        span: SourceSpan,
        stmts: Vec<Stmt>,
    },
    Type(TypeDef),
    TypeAlias {
        span: SourceSpan,
        name: String,
        name_span: SourceSpan,
        params: Vec<String>,
        ty: Type,
    },
    Extern {
        span: SourceSpan,
        name: String,
        name_span: SourceSpan,
        ty: Type,
        kind: ExternKind,
    },
    Expr(Expr),
}

impl Stmt {
    pub fn span(&self) -> SourceSpan {
        match self {
            Stmt::Let { span, .. }
            | Stmt::Fn { span, .. }
            | Stmt::Op { span, .. }
            | Stmt::TypeAlias { span, .. }
            | Stmt::Extern { span, .. } => *span,
            Stmt::Trait(td) => td.span,
            Stmt::Impl(id) => id.span,
            Stmt::InherentImpl(id) => id.span,
            Stmt::TestBlock { span, .. } => *span,
            Stmt::RecBlock { span, .. } => *span,
            Stmt::Type(td) => td.span,
            Stmt::Expr(expr) => expr.span,
        }
    }

    pub fn is_test_fn(&self) -> bool {
        match self {
            Stmt::Fn { attrs, .. } => attrs.iter().any(|attr| attr.is("test")),
            _ => false,
        }
    }
}

/// Visits every expression in a program, including expressions inside nested
/// blocks, functions, operators, and impl methods.
pub fn walk_program_exprs(program: &Program, visit: &mut impl FnMut(&Expr)) {
    for stmt in &program.stmts {
        walk_stmt_exprs(stmt, visit);
    }
}

/// Visits every expression owned by a statement.
pub fn walk_stmt_exprs(stmt: &Stmt, visit: &mut impl FnMut(&Expr)) {
    match stmt {
        Stmt::Let { value, .. } | Stmt::Expr(value) => walk_expr(value, visit),
        Stmt::Fn { body, .. } | Stmt::Op { body, .. } => walk_expr(body, visit),
        Stmt::Impl(id) => {
            for method in &id.methods {
                walk_expr(&method.body, visit);
            }
        }
        Stmt::InherentImpl(id) => {
            for method in &id.methods {
                walk_expr(&method.body, visit);
            }
        }
        Stmt::TestBlock { stmts, .. } => {
            for stmt in stmts {
                walk_stmt_exprs(stmt, visit);
            }
        }
        Stmt::RecBlock { stmts, .. } => {
            for stmt in stmts {
                walk_stmt_exprs(stmt, visit);
            }
        }
        Stmt::Type(_) | Stmt::TypeAlias { .. } | Stmt::Trait(_) | Stmt::Extern { .. } => {}
    }
}

/// Pre-order expression traversal.
pub fn walk_expr(expr: &Expr, visit: &mut impl FnMut(&Expr)) {
    visit(expr);
    match &expr.kind {
        ExprKind::Grouped(inner)
        | ExprKind::Not(inner)
        | ExprKind::Loop(inner)
        | ExprKind::Break(Some(inner))
        | ExprKind::Return(Some(inner))
        | ExprKind::FieldAccess { expr: inner, .. }
        | ExprKind::Lambda { body: inner, .. } => walk_expr(inner, visit),
        ExprKind::Neg { operand, .. } => walk_expr(operand, visit),
        ExprKind::Index { receiver, key, .. } => {
            walk_expr(receiver, visit);
            walk_expr(key, visit);
        }
        ExprKind::Assign { target, value } => {
            walk_expr(target, visit);
            walk_expr(value, visit);
        }
        ExprKind::Binary { lhs, rhs, .. } => {
            walk_expr(lhs, visit);
            walk_expr(rhs, visit);
        }
        ExprKind::Range { start, end, .. } => {
            if let Some(start) = start {
                walk_expr(start, visit);
            }
            if let Some(end) = end {
                walk_expr(end, visit);
            }
        }
        ExprKind::Call { callee, args, .. } => {
            walk_expr(callee, visit);
            for arg in args {
                walk_expr(arg, visit);
            }
        }
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
        } => {
            walk_expr(cond, visit);
            walk_expr(then_branch, visit);
            walk_expr(else_branch, visit);
        }
        ExprKind::Match { scrutinee, arms } => {
            walk_expr(scrutinee, visit);
            for (_, body) in arms {
                walk_expr(body, visit);
            }
        }
        ExprKind::Block { stmts, final_expr } => {
            for stmt in stmts {
                walk_stmt_exprs(stmt, visit);
            }
            if let Some(expr) = final_expr {
                walk_expr(expr, visit);
            }
        }
        ExprKind::Tuple(items) => {
            for item in items {
                walk_expr(item, visit);
            }
        }
        ExprKind::Array(entries) => {
            for entry in entries {
                walk_expr(entry.expr(), visit);
            }
        }
        ExprKind::Record(entries) => {
            for entry in entries {
                walk_expr(entry.expr(), visit);
            }
        }
        ExprKind::For { iterable, body, .. } => {
            walk_expr(iterable, visit);
            walk_expr(body, visit);
        }
        ExprKind::Break(None)
        | ExprKind::Return(None)
        | ExprKind::Continue
        | ExprKind::Number(_)
        | ExprKind::StringLit(_)
        | ExprKind::Bool(_)
        | ExprKind::Ident(_)
        | ExprKind::AssociatedAccess { .. }
        | ExprKind::Import(_)
        | ExprKind::Unit => {}
    }
}

#[derive(Debug, Clone)]
pub struct TypeBound {
    pub args: Vec<Type>,
    pub fundep_arrow_index: Option<usize>,
    pub traits: Vec<String>,
}

#[derive(Debug, Clone)]
pub enum ExternKind {
    Value(String),
    Template(String),
}

#[derive(Debug, Clone)]
pub struct PendingDictArg {
    pub var: u32,
    pub trait_name: String,
    pub args: Vec<crate::types::Ty>,
    pub determinant_indexes: Vec<usize>,
}

#[derive(Debug, Clone)]
pub enum DictRef {
    Param(String),
    Concrete(String),
    Applied { dict: String, args: Vec<DictRef> },
    Structural(StructuralDictRef),
}

#[derive(Debug, Clone)]
pub struct StructuralDictRef {
    pub trait_name: String,
    pub target: DictTarget,
    pub args: Vec<DictRef>,
}

#[derive(Debug, Clone)]
pub enum DictTarget {
    Tuple(usize),
}

#[derive(Debug, Clone)]
pub enum ResolvedCallee {
    Function(String),
    InherentMethod { dict: String, method: String },
    DictMethod { dict: DictRef, method: String },
}

#[derive(Debug, Clone)]
pub enum AssociatedAccessResolution {
    Inherent(ResolvedCallee),
    TraitMethod {
        method: String,
        dict: Option<DictRef>,
    },
}

#[derive(Debug, Clone)]
pub struct ArgWrapper {
    pub dict_args: Vec<DictRef>,
    pub pending_dict_args: Vec<PendingDictArg>,
}

#[derive(Debug, Clone)]
pub struct Param {
    pub pat: Pattern,
    pub ty: Option<Type>,
    pub mut_place: bool,
}

#[derive(Debug, Clone)]
pub struct TypeParam {
    pub ty: Type,
    pub mut_place: bool,
}

#[derive(Debug, Clone)]
pub struct TypeReturn {
    pub ty: Box<Type>,
    pub mut_place: bool,
}

impl TypeReturn {
    pub fn value(ty: Type) -> Self {
        Self {
            ty: Box::new(ty),
            mut_place: false,
        }
    }

    pub fn mut_place(ty: Type) -> Self {
        Self {
            ty: Box::new(ty),
            mut_place: true,
        }
    }
}

impl TypeParam {
    pub fn value(ty: Type) -> Self {
        Self {
            ty,
            mut_place: false,
        }
    }

    pub fn mut_place(ty: Type) -> Self {
        Self {
            ty,
            mut_place: true,
        }
    }
}

impl Param {
    pub fn new(pat: Pattern, ty: Option<Type>) -> Self {
        Self {
            pat,
            ty,
            mut_place: false,
        }
    }

    pub fn mut_place(pat: Pattern, ty: Option<Type>) -> Self {
        Self {
            pat,
            ty,
            mut_place: true,
        }
    }
}

// ── Trait / Impl ──────────────────────────────────────────────────────────────

#[derive(Debug, Clone)]
pub struct TraitMethod {
    pub span: SourceSpan,
    pub name: String,
    pub name_span: SourceSpan,
    pub fixity: Option<(Fixity, u8)>,
    pub params: Vec<(String, Type)>,
    pub ret_type: Type,
    pub inline: bool,
}

#[derive(Debug, Clone)]
pub struct TraitDef {
    pub span: SourceSpan,
    pub name: String,
    pub name_span: SourceSpan,
    /// Legacy unary trait parameter. New code must use `params` or
    /// `primary_param()`; this is only kept while older unary/HKT paths are
    /// being migrated.
    #[deprecated(note = "use TraitDef::params or TraitDef::primary_param()")]
    pub param: String,
    pub params: Vec<String>,
    pub fundeps: Vec<FunctionalDependency>,
    pub methods: Vec<TraitMethod>,
}

impl TraitDef {
    pub fn primary_param(&self) -> Option<&str> {
        self.params.first().map(String::as_str)
    }

    pub fn is_unary(&self) -> bool {
        self.params.len() == 1 && self.fundeps.is_empty()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FunctionalDependency {
    pub determinants: Vec<usize>,
    pub dependents: Vec<usize>,
}

#[derive(Debug, Clone)]
pub struct ImplMethod {
    pub span: SourceSpan,
    pub name: String,
    pub name_span: SourceSpan,
    pub params: Vec<Param>,
    pub ret_type: Option<TypeReturn>,
    pub body: Expr,
    pub inline: bool,
}

#[derive(Debug, Clone)]
pub struct ImplDef {
    pub span: SourceSpan,
    pub trait_name: String,
    /// Legacy unary impl target. New code must use `trait_args`; this is only
    /// kept while older inherent/unary trait paths are being migrated.
    #[deprecated(note = "use ImplDef::trait_args")]
    pub target: Type,
    pub trait_args: Vec<Type>,
    pub dict_arg_indexes: Vec<usize>,
    pub used_fundep_arrow: bool,
    pub fundep_arrow_index: Option<usize>,
    pub type_bounds: Vec<TypeBound>,
    pub dict_params: Vec<String>,
    pub methods: Vec<ImplMethod>,
    pub generated_by: Option<GeneratedBy>,
}

impl ImplDef {
    pub fn unary_target(&self) -> Option<&Type> {
        if self.trait_args.len() == 1 {
            self.trait_args.first()
        } else {
            None
        }
    }
}

#[derive(Debug, Clone)]
pub struct InherentMethod {
    pub span: SourceSpan,
    pub name: String,
    pub name_span: SourceSpan,
    pub params: Vec<Param>,
    pub ret_type: Option<TypeReturn>,
    pub body: Expr,
    pub dict_params: Vec<String>,
    pub type_bounds: Vec<TypeBound>,
}

#[derive(Debug, Clone)]
pub struct InherentImplDef {
    pub span: SourceSpan,
    pub target: Type,
    pub type_bounds: Vec<TypeBound>,
    pub methods: Vec<InherentMethod>,
}

// ── Sum types ─────────────────────────────────────────────────────────────────

#[derive(Debug, Clone)]
pub struct Variant {
    pub span: SourceSpan,
    pub name: String,
    pub name_span: SourceSpan,
    pub payload: Option<Type>,
}

#[derive(Debug, Clone)]
pub struct TypeDef {
    pub span: SourceSpan,
    pub name: String,
    pub name_span: SourceSpan,
    /// Type parameters, e.g. `["'a", "'b"]` for `type Result['a, 'b]`
    pub params: Vec<String>,
    pub variants: Vec<Variant>,
    /// Derive metadata parsed from source. The derive expansion pass drains this
    /// field after inserting generated impls, making the pass idempotent.
    pub derives: Vec<DeriveAttr>,
}

// ── Patterns ──────────────────────────────────────────────────────────────────

/// `None`=closed, `Some(None)`=`..`, `Some(Some((s, span)))`=`..s`
pub type RestPat = Option<Option<(String, SourceSpan)>>;

#[derive(Debug, Clone)]
pub enum Pattern {
    /// `_`
    Wildcard,
    /// String literal, e.g. `"("`
    StringLit(String),
    /// Numeric literal, e.g. `0` or `0.0`.
    NumberLit(NumberLiteral),
    /// Boolean literal, e.g. `true`.
    BoolLit(bool),
    /// Integer range literal, e.g. `1..5` or `1..=5`.
    IntRange {
        start: i32,
        end: i32,
        inclusive: bool,
    },
    /// A simple variable binding, e.g. `x` in `for x in arr`.
    /// The `SourceSpan` is the span of the binding name in source.
    Variable(String, SourceSpan),
    /// `Some(x)`, `Ok((next, value))`, or `None`.
    Constructor {
        name: String,
        binding: Option<Box<Pattern>>,
    },
    /// `#{ field }`, `#{ field, .. }`, `#{ x: alias, ..rest }`.
    /// Each entry is `(field_name, binding_name, binding_span)`.
    Record {
        fields: Vec<(String, String, SourceSpan)>,
        rest: RestPat,
    },
    /// `[]`, `[a]`, `[(a, b)]`, `[a, ..]`, `[a, b, ..rest]`.
    List {
        elements: Vec<Pattern>,
        rest: RestPat,
    },
    /// `(a, b, c)` — positional tuple destructuring, mirroring `Ty::Tuple`.
    Tuple(Vec<Pattern>),
}

// ── Spread entries ───────────────────────────────────────────────────────────

#[derive(Debug, Clone)]
pub enum ArrayEntry {
    Elem(Expr),
    Spread(Expr),
}

impl ArrayEntry {
    pub fn expr(&self) -> &Expr {
        match self {
            Self::Elem(e) | Self::Spread(e) => e,
        }
    }
    pub fn expr_mut(&mut self) -> &mut Expr {
        match self {
            Self::Elem(e) | Self::Spread(e) => e,
        }
    }
}

#[derive(Debug, Clone)]
pub enum RecordEntry {
    Field(String, Expr),
    Spread(Expr),
}

impl RecordEntry {
    pub fn expr(&self) -> &Expr {
        match self {
            Self::Field(_, e) | Self::Spread(e) => e,
        }
    }
    pub fn expr_mut(&mut self) -> &mut Expr {
        match self {
            Self::Field(_, e) | Self::Spread(e) => e,
        }
    }
}

// ── Expressions ───────────────────────────────────────────────────────────────

#[derive(Debug, Clone)]
pub struct Expr {
    pub id: NodeId,
    pub span: SourceSpan,
    pub kind: ExprKind,
}

impl Expr {
    pub fn new(id: NodeId, span: SourceSpan, kind: ExprKind) -> Self {
        Self { id, span, kind }
    }

    pub fn synthetic(kind: ExprKind) -> Self {
        Self {
            id: 0,
            span: SourceSpan::synthetic(),
            kind,
        }
    }
}

#[derive(Debug, Clone)]
pub enum ExprKind {
    Number(NumberLiteral),
    StringLit(String),
    Bool(bool),
    Ident(String),
    /// A parenthesized expression whose grouping must survive AST rewrites.
    ///
    /// This is semantically transparent for type checking and code generation,
    /// but it is a hard boundary for precedence-sensitive rewrites such as
    /// custom operator reassociation.
    Grouped(Box<Expr>),
    Not(Box<Expr>),
    Neg {
        operand: Box<Expr>,
        /// Source span of the unary `-` token itself, used for hover.
        op_span: SourceSpan,
        resolved_op: Option<ResolvedCallee>,
        pending_op: Option<PendingDictArg>,
    },
    Assign {
        target: Box<Expr>,
        value: Box<Expr>,
    },
    Binary {
        lhs: Box<Expr>,
        op: BinOp,
        /// Source span of the operator token itself, used for hover.
        op_span: SourceSpan,
        rhs: Box<Expr>,
        resolved_op: Option<ResolvedCallee>,
        pending_op: Option<PendingDictArg>,
        dict_args: Vec<DictRef>,
        pending_dict_args: Vec<PendingDictArg>,
    },
    Range {
        start: Option<Box<Expr>>,
        end: Option<Box<Expr>>,
        inclusive: bool,
    },
    Call {
        callee: Box<Expr>,
        args: Vec<Expr>,
        is_method_call: bool,
        arg_wrappers: Vec<Option<ArgWrapper>>,
        /// Resolved callee for trait methods, e.g. `__Functor__Option.map`
        resolved_callee: Option<ResolvedCallee>,
        pending_trait_method: Option<(PendingDictArg, String)>,
        dict_args: Vec<DictRef>,
        pending_dict_args: Vec<PendingDictArg>,
    },
    If {
        cond: Box<Expr>,
        then_branch: Box<Expr>,
        else_branch: Box<Expr>,
    },
    Match {
        scrutinee: Box<Expr>,
        arms: Vec<(Pattern, Expr)>,
    },
    Loop(Box<Expr>),
    Break(Option<Box<Expr>>),
    Continue,
    Return(Option<Box<Expr>>),
    Block {
        stmts: Vec<Stmt>,
        final_expr: Option<Box<Expr>>,
    },
    Tuple(Vec<Expr>),
    Array(Vec<ArrayEntry>),
    Record(Vec<RecordEntry>),
    FieldAccess {
        expr: Box<Expr>,
        field: String,
        field_span: SourceSpan,
    },
    Index {
        receiver: Box<Expr>,
        key: Box<Expr>,
        resolved_callee: Option<ResolvedCallee>,
        pending_trait_method: Option<(PendingDictArg, String)>,
        dict_args: Vec<DictRef>,
        pending_dict_args: Vec<PendingDictArg>,
    },
    AssociatedAccess {
        target: Type,
        target_span: SourceSpan,
        member: String,
        member_span: SourceSpan,
        resolution: Option<AssociatedAccessResolution>,
    },
    Import(String),
    Lambda {
        params: Vec<Param>,
        return_type: Option<Type>,
        body: Box<Expr>,
        dict_params: Vec<String>,
    },
    For {
        pat: Pattern,
        iterable: Box<Expr>,
        body: Box<Expr>,
        resolved_iter: Option<ResolvedCallee>,
        pending_iter: Option<PendingDictArg>,
    },
    Unit,
}

#[derive(Debug, Clone)]
pub enum BinOp {
    Pipe,
    Custom(String),
}

// ── Types ─────────────────────────────────────────────────────────────────────

#[derive(Debug, Clone)]
pub enum Type {
    Ident(String),
    App(Box<Type>, Vec<Type>),
    Var(String),
    Func(Vec<TypeParam>, TypeReturn),
    Tuple(Vec<Type>),
    Record(Vec<(String, Type)>, bool),
    Unit,
    Never,
    /// Hole marker `*` in impl heads
    Hole,
}
