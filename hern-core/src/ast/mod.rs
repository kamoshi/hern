use crate::lex::error::Span;

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

#[derive(Debug, Clone)]
pub struct Program {
    pub stmts: Vec<Stmt>,
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
        span: SourceSpan,
        name: String,
        name_span: SourceSpan,
        params: Vec<(Pattern, Option<Type>)>,
        ret_type: Option<Type>,
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
        params: Vec<(Pattern, Option<Type>)>,
        ret_type: Option<Type>,
        body: Expr,
        dict_params: Vec<String>,
        type_bounds: Vec<TypeBound>,
    },
    Trait(TraitDef),
    Impl(ImplDef),
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
            Stmt::Type(td) => td.span,
            Stmt::Expr(expr) => expr.span,
        }
    }
}

#[derive(Debug, Clone)]
pub struct TypeBound {
    pub var: String,
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
    pub param: String,
    pub methods: Vec<TraitMethod>,
}

#[derive(Debug, Clone)]
pub struct ImplMethod {
    pub span: SourceSpan,
    pub name: String,
    pub name_span: SourceSpan,
    pub params: Vec<(Pattern, Option<Type>)>,
    pub ret_type: Option<Type>,
    pub body: Expr,
    pub inline: bool,
}

#[derive(Debug, Clone)]
pub struct ImplDef {
    pub span: SourceSpan,
    pub trait_name: String,
    pub target: Type,
    pub methods: Vec<ImplMethod>,
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
    /// A simple variable binding, e.g. `x` in `for x in arr`.
    /// The `SourceSpan` is the span of the binding name in source.
    Variable(String, SourceSpan),
    /// `Some(x)` or `None`.
    /// When a binding is present, its `SourceSpan` covers the bound name.
    Constructor {
        name: String,
        binding: Option<(String, SourceSpan)>,
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
    Number(f64),
    StringLit(String),
    Bool(bool),
    Ident(String),
    Not(Box<Expr>),
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
        resolved_op: Option<String>,
        pending_op: Option<PendingDictArg>,
        dict_args: Vec<String>,
        pending_dict_args: Vec<PendingDictArg>,
    },
    Call {
        callee: Box<Expr>,
        args: Vec<Expr>,
        /// Resolved callee for trait methods, e.g. `__Functor__Option.map`
        resolved_callee: Option<String>,
        dict_args: Vec<String>,
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
    Array(Vec<Expr>),
    Record(Vec<(String, Expr)>),
    FieldAccess {
        expr: Box<Expr>,
        field: String,
        field_span: SourceSpan,
    },
    Import(String),
    Lambda {
        params: Vec<(Pattern, Option<Type>)>,
        body: Box<Expr>,
        dict_params: Vec<String>,
    },
    For {
        pat: Pattern,
        iterable: Box<Expr>,
        body: Box<Expr>,
        resolved_iter: Option<String>,
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
    Func(Vec<Type>, Box<Type>),
    Tuple(Vec<Type>),
    Record(Vec<(String, Type)>, bool),
    Unit,
    /// Hole marker `*` in impl heads
    Hole,
}
