use crate::ast::*;
use crate::lex::error::{ParseError, Span};
use crate::lex::{NumberLiteral, Spanned, Token};
use std::cell::{Cell, RefCell};

type FnParamsBody = (usize, Vec<Param>, Option<TypeReturn>, Vec<TypeBound>, Expr);

fn is_alias_token(token: &Token) -> bool {
    matches!(token, Token::Ident(name) if name == "alias")
}

fn is_test_token(token: &Token) -> bool {
    matches!(token, Token::Ident(name) if name == "test")
}

fn is_and_token(token: &Token) -> bool {
    matches!(token, Token::Ident(name) if name == "and")
}

fn attr_error_span(attr: &Attribute) -> Span {
    Span {
        line: attr.span.start_line,
        col: attr.span.start_col,
        len: attr.span.end_col.saturating_sub(attr.span.start_col),
    }
}

fn starts_statement_or_item(token: &Token) -> bool {
    matches!(
        token,
        Token::Let
            | Token::Fn
            | Token::Trait
            | Token::Impl
            | Token::Type
            | Token::Extern
            | Token::Import
            | Token::Do
            | Token::Return
            | Token::Break
            | Token::Continue
            | Token::If
            | Token::Match
            | Token::Loop
    ) || is_test_token(token)
}

fn negate_number_literal(number: &NumberLiteral) -> NumberLiteral {
    match number {
        NumberLiteral::Int(value) => NumberLiteral::Int(value.saturating_neg()),
        NumberLiteral::Float(value) => NumberLiteral::Float(-value),
    }
}

fn parse_signed_int_pattern_bound(
    tokens: &[Spanned],
    fallback_span: Span,
) -> Result<(usize, i32), ParseError> {
    let Some(first) = tokens.first() else {
        return Err(ParseError::new(
            "range pattern requires an end bound",
            fallback_span,
        ));
    };
    let (sign, number_index, span) = if first.token == Token::Minus {
        let Some(next) = tokens.get(1) else {
            return Err(ParseError::new(
                "Expected integer after `-` in range pattern",
                first.span,
            ));
        };
        (-1, 1, next.span)
    } else {
        (1, 0, first.span)
    };

    let Token::Number(NumberLiteral::Int(value)) = &tokens[number_index].token else {
        return Err(ParseError::new(
            "range patterns require integer bounds",
            span,
        ));
    };

    Ok((number_index + 1, value.saturating_mul(sign)))
}

fn consumed_span(tokens: &[Spanned], consumed: usize) -> SourceSpan {
    let start = tokens.first().map(|token| token.span).unwrap_or(Span {
        line: 0,
        col: 0,
        len: 0,
    });
    let end = tokens
        .get(consumed.saturating_sub(1))
        .map(|token| token.span)
        .unwrap_or(start);
    SourceSpan::from_bounds(start, end)
}

/// For simple patterns (`Variable`, `Wildcard`) that were parsed without span context (e.g.
/// `parse_for_pattern`), back-fill the span from the surrounding token range.
/// For patterns that already carry their own per-binding spans (`Constructor`, `Record`,
/// `List`) this is a no-op.
fn apply_span_to_pattern(pat: Pattern, _span: SourceSpan) -> Pattern {
    match pat {
        // Variable span is set in parse_for_pattern already; keep it.
        Pattern::Variable(_, _) => pat,
        // Wildcard has no binding to track.
        Pattern::Wildcard => pat,
        // Complex patterns carry their own per-binding spans from parse_pattern.
        other => other,
    }
}

fn infix_binary_op(token: &Token) -> Option<(BinOp, u8, u8)> {
    let (op, l_bp, r_bp) = match token {
        Token::PipeArrow => (BinOp::Pipe, 2, 3),
        Token::PipePipe => (BinOp::Custom("||".to_string()), 3, 4),
        Token::AmpAmp => (BinOp::Custom("&&".to_string()), 5, 6),
        Token::EqEq => (BinOp::Custom("==".to_string()), 4, 5),
        Token::BangEq => (BinOp::Custom("!=".to_string()), 4, 5),
        Token::Plus => (BinOp::Custom("+".to_string()), 9, 10),
        Token::Minus => (BinOp::Custom("-".to_string()), 9, 10),
        Token::Star => (BinOp::Custom("*".to_string()), 11, 12),
        Token::Op(op) if op == "**" => (BinOp::Custom(op.clone()), 13, 13),
        Token::Op(op) => (BinOp::Custom(op.clone()), 6, 7),
        _ => return None,
    };
    Some((op, l_bp, r_bp))
}

fn can_end_range(tokens: &[Spanned], ptr: usize) -> bool {
    matches!(
        tokens.get(ptr).map(|t| &t.token),
        None | Some(
            Token::Eof
                | Token::Semicolon
                | Token::Comma
                | Token::RParen
                | Token::RBracket
                | Token::RBrace
        )
    )
}

fn associated_target_from_expr(
    expr: &Expr,
    op_span: Span,
    allow_hole: bool,
) -> Result<Type, ParseError> {
    match &expr.kind {
        ExprKind::Ident(name) if name == "_" && allow_hole => Ok(Type::Hole),
        ExprKind::Ident(name) if name == "_" => Err(ParseError::new(
            "`_` is only allowed inside an explicit associated type target",
            op_span,
        )),
        ExprKind::Ident(name) if name.starts_with('\'') => Ok(Type::Var(name.clone())),
        ExprKind::Ident(name) => Ok(Type::Ident(name.clone())),
        ExprKind::Call { callee, args, .. } => {
            let con = associated_target_from_expr(callee, op_span, false)?;
            let args = args
                .iter()
                .map(|arg| associated_target_from_expr(arg, op_span, true))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(Type::App(Box::new(con), args))
        }
        _ => Err(ParseError::new(
            "`::` expects a type name or applied type on the left",
            op_span,
        )),
    }
}

fn recover_stmt_tokens(tokens: &[Spanned]) -> usize {
    let mut parens = 0usize;
    let mut braces = 0usize;
    let mut brackets = 0usize;

    for (idx, token) in tokens.iter().enumerate().skip(1) {
        match token.token {
            Token::LParen => parens += 1,
            Token::RParen => parens = parens.saturating_sub(1),
            Token::LBrace => braces += 1,
            Token::RBrace => {
                if parens == 0 && brackets == 0 && braces == 0 {
                    return idx + 1;
                }
                braces = braces.saturating_sub(1);
            }
            Token::LBracket => brackets += 1,
            Token::RBracket => brackets = brackets.saturating_sub(1),
            Token::Semicolon if parens == 0 && braces == 0 && brackets == 0 => return idx + 1,
            Token::Let | Token::Fn | Token::Trait | Token::Impl | Token::Type | Token::Extern
                if parens == 0 && braces == 0 && brackets == 0 =>
            {
                return idx;
            }
            _ if is_test_token(&token.token) && parens == 0 && braces == 0 && brackets == 0 => {
                return idx;
            }
            Token::Eof => return idx,
            _ => {}
        }
    }

    tokens.len()
}

/// Internal representation of a single line inside a `do { }` block.
/// Never escapes the parser — `desugar_do` converts these into ordinary AST nodes.
enum DoStmt {
    /// `let [mut] pat [: ty] <- expr ;`  — monadic bind
    /// Fields: (pat, is_mutable, ty, arrow_span, monad_expr)
    Bind(Pattern, bool, Option<Type>, SourceSpan, Expr),
    /// `let [mut] pat [: ty] = expr ;`   — plain let binding
    /// Fields: (pat, is_mutable, ty, stmt_span, value)
    Let(Pattern, bool, Option<Type>, SourceSpan, Expr),
    /// `expr ;`                           — sequencing (result discarded)
    Bare(Expr),
}

/// Recursively checks that `expr` contains no control-flow that would silently
/// misbehave across the hidden lambda boundary introduced by `do` desugaring.
///
/// * `return` is always forbidden — loops compile without an IIFE, so `return`
///   inside any loop body still reaches the hidden lambda, not the real function.
/// * `break` / `continue` are forbidden unless we are already inside an explicit
///   `loop { }` or `for … in … { }` (whose `goto` targets are inside the lambda).
///
/// Recursion stops at `ExprKind::Lambda` for all three keywords (user-written
/// functions are a real boundary), and additionally at loop bodies for
/// `break`/`continue`.
fn check_do_control_flow(expr: &Expr, in_explicit_loop: bool) -> Result<(), ParseError> {
    match &expr.kind {
        ExprKind::Return(_) => Err(ParseError::new(
            "`return` is not allowed inside a `do` block",
            Span { line: expr.span.start_line, col: expr.span.start_col, len: 6 },
        )),
        ExprKind::Break(_) if !in_explicit_loop => Err(ParseError::new(
            "`break` is not allowed inside a `do` block",
            Span { line: expr.span.start_line, col: expr.span.start_col, len: 5 },
        )),
        ExprKind::Continue if !in_explicit_loop => Err(ParseError::new(
            "`continue` is not allowed inside a `do` block",
            Span { line: expr.span.start_line, col: expr.span.start_col, len: 8 },
        )),

        // Explicit function boundary — stop all checks.
        ExprKind::Lambda { .. } => Ok(()),

        // Explicit loop boundary — break/continue are now safe inside; return still propagates.
        ExprKind::Loop(body) => check_do_control_flow(body, true),
        ExprKind::For { iterable, body, .. } => {
            check_do_control_flow(iterable, in_explicit_loop)?;
            check_do_control_flow(body, true)
        }

        // Blocks: visit statement values and the tail expression.
        // Fn / Op bodies open new function scopes — do not descend into them.
        ExprKind::Block { stmts, final_expr } => {
            for stmt in stmts {
                match stmt {
                    Stmt::Let { value, .. } => check_do_control_flow(value, in_explicit_loop)?,
                    Stmt::Expr(e) => check_do_control_flow(e, in_explicit_loop)?,
                    _ => {}
                }
            }
            if let Some(e) = final_expr {
                check_do_control_flow(e, in_explicit_loop)?;
            }
            Ok(())
        }

        // All other expression forms: recurse with the same loop context.
        ExprKind::Grouped(e) | ExprKind::Not(e) => check_do_control_flow(e, in_explicit_loop),
        ExprKind::Neg { operand, .. } => check_do_control_flow(operand, in_explicit_loop),
        ExprKind::Assign { target, value } => {
            check_do_control_flow(target, in_explicit_loop)?;
            check_do_control_flow(value, in_explicit_loop)
        }
        ExprKind::Binary { lhs, rhs, .. } => {
            check_do_control_flow(lhs, in_explicit_loop)?;
            check_do_control_flow(rhs, in_explicit_loop)
        }
        ExprKind::Range { start, end, .. } => {
            if let Some(start) = start {
                check_do_control_flow(start, in_explicit_loop)?;
            }
            if let Some(end) = end {
                check_do_control_flow(end, in_explicit_loop)?;
            }
            Ok(())
        }
        ExprKind::Call { callee, args, .. } => {
            check_do_control_flow(callee, in_explicit_loop)?;
            for arg in args {
                check_do_control_flow(arg, in_explicit_loop)?;
            }
            Ok(())
        }
        ExprKind::If { cond, then_branch, else_branch } => {
            check_do_control_flow(cond, in_explicit_loop)?;
            check_do_control_flow(then_branch, in_explicit_loop)?;
            check_do_control_flow(else_branch, in_explicit_loop)
        }
        ExprKind::Match { scrutinee, arms } => {
            check_do_control_flow(scrutinee, in_explicit_loop)?;
            for (_, body) in arms {
                check_do_control_flow(body, in_explicit_loop)?;
            }
            Ok(())
        }
        ExprKind::Tuple(es) => {
            for e in es {
                check_do_control_flow(e, in_explicit_loop)?;
            }
            Ok(())
        }
        ExprKind::Array(entries) => {
            for entry in entries {
                check_do_control_flow(entry.expr(), in_explicit_loop)?;
            }
            Ok(())
        }
        ExprKind::Record(entries) => {
            for entry in entries {
                check_do_control_flow(entry.expr(), in_explicit_loop)?;
            }
            Ok(())
        }
        ExprKind::FieldAccess { expr, .. } => check_do_control_flow(expr, in_explicit_loop),
        ExprKind::Index { receiver, key, .. } => {
            check_do_control_flow(receiver, in_explicit_loop)?;
            check_do_control_flow(key, in_explicit_loop)
        }
        // Leaves — no sub-expressions to visit.
        // in_explicit_loop == true (already accepted above); recurse into value
        ExprKind::Break(Some(e)) => check_do_control_flow(e, in_explicit_loop),
        ExprKind::Break(None) => Ok(()),
        ExprKind::Number(_)
        | ExprKind::StringLit(_)
        | ExprKind::Bool(_)
        | ExprKind::Ident(_)
        | ExprKind::Import(_)
        | ExprKind::Unit
        | ExprKind::AssociatedAccess { .. }
        | ExprKind::Continue   // in_explicit_loop == true (already accepted above)
        => Ok(()),
    }
}

pub struct Parser<'tokens> {
    tokens: &'tokens [Spanned],
    next_node_id: Cell<NodeId>,
    /// When true, `parse_block` treats non-semicoloned, non-tail expressions as
    /// discarded statements rather than failing the block parse. This lets the
    /// recovering top-level parser produce a complete function AST even when the
    /// user is mid-edit inside the body.
    recovering: bool,
    /// Diagnostics emitted from within nested constructs during recovery. Block-level
    /// errors (like missing semicolons) are recorded here instead of propagated as
    /// `Err`, so that `parse_program_recovering` can include them in its output.
    inner_diagnostics: RefCell<Vec<ParseError>>,
}

impl<'tokens> Parser<'tokens> {
    pub fn new(tokens: &'tokens [Spanned]) -> Self {
        Self {
            tokens,
            next_node_id: Cell::new(1),
            recovering: false,
            inner_diagnostics: RefCell::new(Vec::new()),
        }
    }

    pub(crate) fn new_recovering(tokens: &'tokens [Spanned]) -> Self {
        Self {
            tokens,
            next_node_id: Cell::new(1),
            recovering: true,
            inner_diagnostics: RefCell::new(Vec::new()),
        }
    }

    fn next_node_id(&self) -> NodeId {
        let id = self.next_node_id.get();
        self.next_node_id.set(id + 1);
        id
    }

    fn expr_from_bounds(&self, start: Span, end: Span, kind: ExprKind) -> Expr {
        Expr::new(
            self.next_node_id(),
            SourceSpan::from_bounds(start, end),
            kind,
        )
    }

    fn expr_from_tokens(&self, tokens: &[Spanned], consumed: usize, kind: ExprKind) -> Expr {
        let start = tokens.first().map(|t| t.span).unwrap_or(Span {
            line: 0,
            col: 0,
            len: 0,
        });
        let end = consumed
            .checked_sub(1)
            .and_then(|idx| tokens.get(idx))
            .map(|t| t.span)
            .unwrap_or(start);
        self.expr_from_bounds(start, end, kind)
    }

    fn parse_inline_attrs(
        &self,
        tokens: &[Spanned],
        mut ptr: usize,
    ) -> Result<(usize, bool), ParseError> {
        let start = ptr;
        let mut inline = false;

        while tokens.get(ptr).map(|t| &t.token) == Some(&Token::Hash)
            && tokens.get(ptr + 1).map(|t| &t.token) == Some(&Token::LBracket)
        {
            ptr += 1;
            ptr += self.expect(&tokens[ptr..], Token::LBracket)?;
            let attr_span = tokens.get(ptr).map(|t| t.span).unwrap_or(Span {
                line: 0,
                col: 0,
                len: 0,
            });
            let (c_attr, attr) = self.expect_ident(&tokens[ptr..])?;
            ptr += c_attr;
            if tokens.get(ptr).map(|t| &t.token) == Some(&Token::LParen) {
                return Err(ParseError::new(
                    format!("Attribute `{}` cannot be used here", attr),
                    attr_span,
                ));
            }
            ptr += self.expect(&tokens[ptr..], Token::RBracket)?;

            if attr == "inline" {
                inline = true;
            } else {
                return Err(ParseError::new(
                    format!("Unknown attribute `{}`", attr),
                    attr_span,
                ));
            }
        }

        Ok((ptr - start, inline))
    }

    fn parse_outer_attrs(
        &self,
        tokens: &[Spanned],
        mut ptr: usize,
    ) -> Result<(usize, Vec<Attribute>), ParseError> {
        let start = ptr;
        let mut attrs = Vec::new();

        while tokens.get(ptr).map(|t| &t.token) == Some(&Token::Hash)
            && tokens.get(ptr + 1).map(|t| &t.token) == Some(&Token::LBracket)
        {
            let attr_start = ptr;
            ptr += 1;
            ptr += self.expect(&tokens[ptr..], Token::LBracket)?;
            let attr_span = tokens.get(ptr).map(|t| t.span).unwrap_or(Span {
                line: 0,
                col: 0,
                len: 0,
            });
            let name = match tokens.get(ptr) {
                Some(Spanned {
                    token: Token::Ident(name),
                    ..
                }) => name.clone(),
                Some(tok) => {
                    return Err(ParseError::new(
                        format!("Expected attribute name, found {}", tok.token),
                        tok.span,
                    ));
                }
                None => return Err(ParseError::new("Unexpected EOF", attr_span)),
            };
            ptr += 1;
            let mut args = Vec::new();
            if tokens.get(ptr).map(|t| &t.token) == Some(&Token::LParen) {
                ptr += 1;
                if tokens.get(ptr).map(|t| &t.token) == Some(&Token::RParen) {
                    return Err(ParseError::new(
                        format!("Attribute `{}` requires at least one argument", name),
                        tokens[ptr].span,
                    ));
                }
                loop {
                    let arg_span = tokens.get(ptr).map(|t| t.span).unwrap_or(attr_span);
                    let arg = match tokens.get(ptr) {
                        Some(Spanned {
                            token: Token::Ident(arg),
                            ..
                        }) => arg.clone(),
                        Some(tok) => {
                            return Err(ParseError::new(
                                format!("Expected attribute argument, found {}", tok.token),
                                tok.span,
                            ));
                        }
                        None => return Err(ParseError::new("Unexpected EOF", arg_span)),
                    };
                    ptr += 1;
                    args.push(arg);
                    if tokens.get(ptr).map(|t| &t.token) == Some(&Token::Comma) {
                        ptr += 1;
                    } else {
                        break;
                    }
                }
                ptr += self.expect(&tokens[ptr..], Token::RParen)?;
            }
            ptr += self.expect(&tokens[ptr..], Token::RBracket)?;
            attrs.push(Attribute {
                name,
                args,
                span: consumed_span(&tokens[attr_start..], ptr - attr_start),
            });
        }

        Ok((ptr - start, attrs))
    }

    fn parse_extern_kind_marker(
        &self,
        tokens: &[Spanned],
        mut ptr: usize,
    ) -> Result<(usize, bool), ParseError> {
        if tokens.get(ptr).map(|t| &t.token) != Some(&Token::Hash) {
            return Ok((0, false));
        }

        let start = ptr;
        ptr += 1;
        ptr += self.expect(&tokens[ptr..], Token::LBracket)?;
        let attr_span = tokens.get(ptr).map(|t| t.span).unwrap_or(Span {
            line: 0,
            col: 0,
            len: 0,
        });
        let (c_attr, attr) = self.expect_ident(&tokens[ptr..])?;
        ptr += c_attr;
        ptr += self.expect(&tokens[ptr..], Token::RBracket)?;

        if attr == "template" {
            Ok((ptr - start, true))
        } else {
            Err(ParseError::new(
                format!("Unknown extern attribute `{}`", attr),
                attr_span,
            ))
        }
    }

    pub fn parse_program(&self) -> Result<Program, ParseError> {
        let mut stmts = Vec::new();
        let mut inner_attrs = Vec::new();
        let mut ptr = 0;

        while let Some(Token::InnerAttr(name)) = self.tokens.get(ptr).map(|t| &t.token) {
            inner_attrs.push(name.clone());
            ptr += 1;
        }

        while ptr < self.tokens.len() && self.tokens[ptr].token != Token::Eof {
            let (consumed, stmt) = self.parse_stmt(&self.tokens[ptr..])?;
            stmts.push(stmt);
            ptr += consumed;
        }

        Ok(Program { stmts, inner_attrs })
    }

    pub fn parse_program_recovering(&self) -> (Program, Vec<ParseError>) {
        let mut stmts = Vec::new();
        let mut inner_attrs = Vec::new();
        let mut diagnostics = Vec::new();
        let mut ptr = 0;

        while let Some(Token::InnerAttr(name)) = self.tokens.get(ptr).map(|t| &t.token) {
            inner_attrs.push(name.clone());
            ptr += 1;
        }

        while ptr < self.tokens.len() && self.tokens[ptr].token != Token::Eof {
            match self.parse_stmt(&self.tokens[ptr..]) {
                Ok((consumed, stmt)) if consumed > 0 => {
                    stmts.push(stmt);
                    ptr += consumed;
                }
                Ok(_) => {
                    ptr += 1;
                }
                Err(err) => {
                    diagnostics.push(err);
                    ptr += recover_stmt_tokens(&self.tokens[ptr..]).max(1);
                }
            }
            // Collect any block-level diagnostics accumulated during recovery
            // (e.g. expressions used as statements without a semicolon).
            diagnostics.append(&mut self.inner_diagnostics.borrow_mut());
        }

        (Program { stmts, inner_attrs }, diagnostics)
    }

    fn parse_stmt(&self, tokens: &[Spanned]) -> Result<(usize, Stmt), ParseError> {
        self.parse_stmt_in_context(tokens, false)
    }

    fn parse_test_block_stmt(&self, tokens: &[Spanned]) -> Result<(usize, Stmt), ParseError> {
        self.parse_stmt_in_context(tokens, true)
    }

    fn parse_stmt_in_context(
        &self,
        tokens: &[Spanned],
        in_test_block: bool,
    ) -> Result<(usize, Stmt), ParseError> {
        let (attrs_consumed, attrs) = self.parse_outer_attrs(tokens, 0)?;
        if attrs_consumed > 0 {
            let Some(tok) = tokens.get(attrs_consumed) else {
                let attr_span = attrs
                    .last()
                    .map(|attr| attr.span)
                    .unwrap_or_else(SourceSpan::synthetic);
                return Err(ParseError::new(
                    "Expected statement after attribute",
                    Span {
                        line: attr_span.end_line,
                        col: attr_span.end_col,
                        len: 1,
                    },
                ));
            };
            if tok.token == Token::Type {
                if in_test_block {
                    return Err(ParseError::new(
                        "Type declarations are not allowed inside `test` blocks",
                        tok.span,
                    ));
                }
                if let Some(attr) = attrs.iter().find(|attr| !attr.is("derive")) {
                    return Err(ParseError::new(
                        format!(
                            "Attribute `{}` is not allowed on type declarations",
                            attr.name
                        ),
                        attr_error_span(attr),
                    ));
                }
                let (consumed, stmt) =
                    self.parse_type_def_stmt_with_attrs(&tokens[attrs_consumed..], attrs)?;
                return Ok((attrs_consumed + consumed, stmt));
            }
            if let Some(attr) = attrs.iter().find(|attr| !attr.is("test")) {
                let message = if attr.is("derive") {
                    "Attribute `derive` is only allowed on type declarations".to_string()
                } else {
                    format!("Unknown attribute `{}`", attr.name)
                };
                return Err(ParseError::new(message, attr_error_span(attr)));
            }
            if let Some(attr) = attrs.iter().find(|attr| !attr.args.is_empty()) {
                return Err(ParseError::new(
                    format!("Attribute `{}` does not accept arguments", attr.name),
                    attr_error_span(attr),
                ));
            }
            if !in_test_block {
                return Err(ParseError::new(
                    "Attribute `test` can only be used inside a `test` block",
                    attr_error_span(&attrs[0]),
                ));
            }
            if tok.token != Token::Fn {
                return Err(ParseError::new(
                    format!(
                        "Attribute `{}` can only be used on functions",
                        attrs[0].name
                    ),
                    attr_error_span(&attrs[0]),
                ));
            }
            let (consumed, stmt) =
                self.parse_fn_group_stmt_with_attrs(&tokens[attrs_consumed..], attrs)?;
            return Ok((attrs_consumed + consumed, stmt));
        }

        let tok = tokens.first().ok_or_else(|| {
            ParseError::new(
                "Unexpected EOF",
                Span {
                    line: 0,
                    col: 0,
                    len: 0,
                },
            )
        })?;
        match &tok.token {
            Token::Let => self.parse_let_stmt(tokens),
            Token::Fn => self.parse_fn_group_stmt(tokens),
            _ if is_test_token(&tok.token)
                && tokens.get(1).map(|tok| &tok.token) == Some(&Token::LBrace) =>
            {
                self.parse_test_stmt(tokens)
            }
            Token::Trait => self.parse_trait_stmt(tokens),
            Token::Impl => self.parse_impl_stmt(tokens),
            Token::Type => self.parse_type_def_stmt(tokens),
            Token::Extern => self.parse_extern_stmt(tokens),
            _ => {
                let (consumed, expr) = self.parse_expr(tokens, 0)?;
                let mut total_consumed = consumed;
                if let Some(tok) = tokens.get(total_consumed)
                    && tok.token == Token::Semicolon
                {
                    total_consumed += 1;
                }
                Ok((total_consumed, Stmt::Expr(expr)))
            }
        }
    }

    fn parse_test_stmt(&self, tokens: &[Spanned]) -> Result<(usize, Stmt), ParseError> {
        let mut ptr = 0;
        if !tokens.get(ptr).is_some_and(|tok| is_test_token(&tok.token)) {
            return Err(ParseError::new(
                "Expected `test`",
                tokens.get(ptr).map(|t| t.span).unwrap_or(Span {
                    line: 0,
                    col: 0,
                    len: 0,
                }),
            ));
        }
        ptr += 1;
        ptr += self.expect(&tokens[ptr..], Token::LBrace)?;
        let mut stmts = Vec::new();
        while tokens.get(ptr).map(|t| &t.token) != Some(&Token::RBrace) {
            if tokens.get(ptr).map(|t| &t.token) == Some(&Token::Eof) {
                return Err(ParseError::new(
                    "Expected `}` to close test block",
                    tokens[ptr].span,
                ));
            }
            match tokens.get(ptr).map(|t| &t.token) {
                Some(Token::Fn | Token::Hash | Token::Let) => {
                    let (consumed, stmt) = self.parse_test_block_stmt(&tokens[ptr..])?;
                    ptr += consumed;
                    stmts.push(stmt);
                }
                Some(token) if is_test_token(token) => {
                    return Err(ParseError::new(
                        "`test` blocks cannot be nested",
                        tokens[ptr].span,
                    ));
                }
                Some(_) | None => {
                    return Err(ParseError::new(
                        "Expected function, helper declaration, or `}` inside test block",
                        tokens.get(ptr).map(|t| t.span).unwrap_or(Span {
                            line: 0,
                            col: 0,
                            len: 0,
                        }),
                    ));
                }
            }
        }
        ptr += self.expect(&tokens[ptr..], Token::RBrace)?;
        Ok((
            ptr,
            Stmt::TestBlock {
                span: consumed_span(tokens, ptr),
                stmts,
            },
        ))
    }

    fn parse_let_stmt(&self, tokens: &[Spanned]) -> Result<(usize, Stmt), ParseError> {
        let mut ptr = 0;
        ptr += self.expect(&tokens[ptr..], Token::Let)?;

        let mut is_mutable = false;
        if tokens.get(ptr).map(|t| &t.token) == Some(&Token::Mut) {
            is_mutable = true;
            ptr += 1;
        }

        let (consumed_pat, pat) = self.parse_for_pattern(&tokens[ptr..])?;
        ptr += consumed_pat;

        let mut ty = None;
        if tokens.get(ptr).map(|t| &t.token) == Some(&Token::Colon) {
            ptr += 1;
            let (consumed_ty, parsed_ty) = self.parse_type(&tokens[ptr..])?;
            ptr += consumed_ty;
            ty = Some(parsed_ty);
        }

        let equal_span = tokens.get(ptr).map(|tok| tok.span);
        ptr += self.expect(&tokens[ptr..], Token::Equal)?;
        self.reject_missing_rhs_before_next_statement(
            tokens,
            ptr,
            equal_span,
            "expected expression after `=` in let binding",
        )?;
        let (consumed_expr, value) = self.parse_expr(&tokens[ptr..], 0)?;
        ptr += consumed_expr;
        ptr += self.expect(&tokens[ptr..], Token::Semicolon)?;
        Ok((
            ptr,
            Stmt::Let {
                span: consumed_span(tokens, ptr),
                pat,
                is_mutable,
                ty,
                value,
            },
        ))
    }

    fn parse_fn_stmt(&self, tokens: &[Spanned]) -> Result<(usize, Stmt), ParseError> {
        self.parse_fn_stmt_with_attrs(tokens, vec![])
    }

    fn parse_fn_group_stmt(&self, tokens: &[Spanned]) -> Result<(usize, Stmt), ParseError> {
        self.parse_fn_group_stmt_with_attrs(tokens, vec![])
    }

    fn parse_fn_group_stmt_with_attrs(
        &self,
        tokens: &[Spanned],
        attrs: Vec<Attribute>,
    ) -> Result<(usize, Stmt), ParseError> {
        let (mut ptr, first) = self.parse_fn_stmt_with_attrs(tokens, attrs)?;
        let mut fns = vec![first];

        while tokens.get(ptr).is_some_and(|tok| is_and_token(&tok.token))
            && tokens.get(ptr + 1).map(|tok| &tok.token) == Some(&Token::Fn)
        {
            ptr += 1;
            let (consumed, next) = self.parse_fn_stmt(&tokens[ptr..])?;
            match next {
                Stmt::Fn { .. } => {
                    ptr += consumed;
                    fns.push(next);
                }
                Stmt::Op { span, .. } => {
                    return Err(ParseError::new(
                        "`and fn` can only continue ordinary function declarations",
                        Span {
                            line: span.start_line,
                            col: span.start_col,
                            len: span.end_col.saturating_sub(span.start_col),
                        },
                    ));
                }
                _ => unreachable!("parse_fn_stmt only returns function-like statements"),
            }
        }

        if fns.len() == 1 {
            return Ok((ptr, fns.remove(0)));
        }

        Ok((
            ptr,
            Stmt::RecBlock {
                span: consumed_span(tokens, ptr),
                stmts: fns,
            },
        ))
    }

    fn parse_fn_stmt_with_attrs(
        &self,
        tokens: &[Spanned],
        attrs: Vec<Attribute>,
    ) -> Result<(usize, Stmt), ParseError> {
        let mut ptr = 0;
        ptr += self.expect(&tokens[ptr..], Token::Fn)?;

        // Operator definition: fn infixl/infixr/infix <prec> <op>(...)
        if let Some(Token::Ident(s)) = tokens.get(ptr).map(|t| &t.token)
            && (s == "infixl" || s == "infixr" || s == "infix")
        {
            if let Some(attr) = attrs.iter().find(|attr| attr.is("test")) {
                return Err(ParseError::new(
                    "Attribute `test` is not supported on operator functions",
                    attr_error_span(attr),
                ));
            }
            let fixity = match s.as_str() {
                "infixl" => Fixity::Left,
                "infixr" => Fixity::Right,
                _ => Fixity::Non,
            };
            ptr += 1;
            let prec_tok = tokens.get(ptr).ok_or_else(|| {
                ParseError::new(
                    "Expected precedence",
                    Span {
                        line: 0,
                        col: 0,
                        len: 0,
                    },
                )
            })?;
            let prec = if let Token::Number(n) = &prec_tok.token {
                n.precedence_value()
            } else {
                return Err(ParseError::new("Expected precedence number", prec_tok.span));
            };
            ptr += 1;
            let (c_name, name, name_span) = self.expect_name_with_span(&tokens[ptr..])?;
            ptr += c_name;

            let (c_tail, params, ret_type, type_bounds, body) =
                self.parse_fn_params_body(&tokens[ptr..])?;
            ptr += c_tail;
            return Ok((
                ptr,
                Stmt::Op {
                    span: consumed_span(tokens, ptr),
                    name,
                    name_span,
                    fixity,
                    prec,
                    params,
                    ret_type,
                    body,
                    dict_params: vec![],
                    type_bounds,
                },
            ));
        }

        let (consumed_name, name, name_span) = self.expect_ident_with_span(&tokens[ptr..])?;
        ptr += consumed_name;

        let (c_tail, params, ret_type, type_bounds, body) =
            self.parse_fn_params_body(&tokens[ptr..])?;
        ptr += c_tail;
        Ok((
            ptr,
            Stmt::Fn {
                attrs,
                span: consumed_span(tokens, ptr),
                name,
                name_span,
                params,
                ret_type,
                body,
                dict_params: vec![],
                type_bounds,
            },
        ))
    }

    fn parse_where_type_bounds(
        &self,
        tokens: &[Spanned],
    ) -> Result<(usize, Vec<TypeBound>), ParseError> {
        let mut ptr = 0;
        let mut bounds = Vec::new();
        if tokens.get(ptr).map(|t| &t.token) != Some(&Token::Where) {
            return Ok((0, bounds));
        }
        ptr += 1;
        loop {
            let mut args = Vec::new();
            let mut fundep_arrow_index = None;
            loop {
                match tokens.get(ptr).map(|t| &t.token) {
                    Some(Token::Colon) => break,
                    Some(Token::Arrow) => {
                        if fundep_arrow_index.is_some() {
                            return Err(ParseError::new(
                                "Expected only one functional dependency arrow in constraint",
                                tokens[ptr].span,
                            ));
                        }
                        if args.is_empty() {
                            return Err(ParseError::new(
                                "Expected at least one determinant type before `->`",
                                tokens[ptr].span,
                            ));
                        }
                        fundep_arrow_index = Some(args.len());
                        ptr += 1;
                    }
                    Some(Token::Comma) | Some(Token::LBrace) | Some(Token::Eof) | None => {
                        let span = self.parse_error_span(tokens, ptr);
                        return Err(ParseError::new(
                            "Expected `:`, `->`, or another type argument in trait constraint",
                            span,
                        ));
                    }
                    _ => {
                        let (consumed, arg) = self.parse_type(&tokens[ptr..])?;
                        ptr += consumed;
                        args.push(arg);
                    }
                }
            }
            if args.is_empty() {
                return Err(ParseError::new(
                    "Expected at least one type argument in trait constraint",
                    self.parse_error_span(tokens, ptr),
                ));
            }
            if fundep_arrow_index == Some(args.len()) {
                let span = self.parse_error_span(tokens, ptr);
                return Err(ParseError::new(
                    "Expected at least one dependent type after `->`",
                    span,
                ));
            }
            ptr += self.expect(&tokens[ptr..], Token::Colon)?;
            let mut traits = Vec::new();
            loop {
                let (c_tr, tr) = self.expect_ident(&tokens[ptr..])?;
                ptr += c_tr;
                traits.push(tr);
                if tokens.get(ptr).map(|t| &t.token) == Some(&Token::Plus) {
                    ptr += 1;
                } else {
                    break;
                }
            }
            bounds.push(TypeBound {
                args,
                fundep_arrow_index,
                traits,
            });
            if tokens.get(ptr).map(|t| &t.token) == Some(&Token::Comma) {
                ptr += 1;
            } else {
                break;
            }
        }
        Ok((ptr, bounds))
    }

    fn parse_fn_params_body(&self, tokens: &[Spanned]) -> Result<FnParamsBody, ParseError> {
        let mut ptr = 0;
        ptr += self.expect(&tokens[ptr..], Token::LParen)?;
        let mut params = Vec::new();
        if tokens.get(ptr).map(|t| &t.token) != Some(&Token::RParen) {
            loop {
                let (consumed, param) = self.parse_param(&tokens[ptr..], true)?;
                ptr += consumed;
                params.push(param);
                if tokens.get(ptr).map(|t| &t.token) == Some(&Token::Comma) {
                    ptr += 1;
                } else {
                    break;
                }
            }
        }
        ptr += self.expect(&tokens[ptr..], Token::RParen)?;
        let mut ret_type = None;
        if tokens.get(ptr).map(|t| &t.token) == Some(&Token::Arrow) {
            ptr += 1;
            let mut ret_mut_place = false;
            if tokens.get(ptr).map(|t| &t.token) == Some(&Token::Mut) {
                ret_mut_place = true;
                ptr += 1;
            }
            let (consumed_ret, parsed_ret) = self.parse_type(&tokens[ptr..])?;
            ptr += consumed_ret;
            ret_type = Some(if ret_mut_place {
                TypeReturn::mut_place(parsed_ret)
            } else {
                TypeReturn::value(parsed_ret)
            });
        }
        let (c_bounds, type_bounds) = self.parse_where_type_bounds(&tokens[ptr..])?;
        ptr += c_bounds;
        let (consumed_body, body) = self.parse_expr(&tokens[ptr..], 0)?;
        ptr += consumed_body;
        Ok((ptr, params, ret_type, type_bounds, body))
    }

    fn parse_param(
        &self,
        tokens: &[Spanned],
        allow_mut_place: bool,
    ) -> Result<(usize, Param), ParseError> {
        let mut ptr = 0;
        let mut mut_place = false;
        if tokens.get(ptr).map(|t| &t.token) == Some(&Token::Mut) {
            if !allow_mut_place {
                return Err(ParseError::new(
                    "`mut` parameters are not supported in this position",
                    tokens[ptr].span,
                ));
            }
            mut_place = true;
            ptr += 1;
        }

        let param_start = ptr;
        let (c_pat, pat) = self.parse_for_pattern(&tokens[ptr..])?;
        ptr += c_pat;
        let param_span = consumed_span(&tokens[param_start..], c_pat);
        let mut p_type = None;
        if tokens.get(ptr).map(|t| &t.token) == Some(&Token::Colon) {
            ptr += 1;
            let (c_type, parsed_type) = self.parse_type(&tokens[ptr..])?;
            ptr += c_type;
            p_type = Some(parsed_type);
        }
        let pat = apply_span_to_pattern(pat, param_span);
        if mut_place && !matches!(pat, Pattern::Variable(_, _)) {
            return Err(ParseError::new(
                "mutable place parameters must bind a single name",
                tokens[param_start].span,
            ));
        }
        let param = if mut_place {
            Param::mut_place(pat, p_type)
        } else {
            Param::new(pat, p_type)
        };
        Ok((ptr, param))
    }

    fn parse_type_def_stmt(&self, tokens: &[Spanned]) -> Result<(usize, Stmt), ParseError> {
        self.parse_type_def_stmt_with_attrs(tokens, vec![])
    }

    fn parse_type_def_stmt_with_attrs(
        &self,
        tokens: &[Spanned],
        attrs: Vec<Attribute>,
    ) -> Result<(usize, Stmt), ParseError> {
        let derives = self.parse_derive_attrs(&attrs)?;
        let mut ptr = 0;
        ptr += self.expect(&tokens[ptr..], Token::Type)?;

        if tokens
            .get(ptr)
            .is_some_and(|tok| is_alias_token(&tok.token))
        {
            if let Some(attr) = attrs.first() {
                return Err(ParseError::new(
                    "derive is not supported for type aliases",
                    attr_error_span(attr),
                ));
            }
            ptr += 1;
            let (consumed, stmt) = self.parse_type_alias_after_keyword(&tokens[ptr..])?;
            return Ok((ptr + consumed, stmt));
        }

        let (c_name, name, name_span) = self.expect_ident_with_span(&tokens[ptr..])?;
        ptr += c_name;

        let (consumed_params, params) = self.parse_type_params(&tokens[ptr..])?;
        ptr += consumed_params;

        let equal_span = tokens.get(ptr).map(|tok| tok.span);
        ptr += self.expect(&tokens[ptr..], Token::Equal)?;
        self.reject_missing_rhs_before_next_statement(
            tokens,
            ptr,
            equal_span,
            "expected type or variant after `=` in type declaration",
        )?;

        // Opaque type: `type Foo('a) = *`
        if tokens.get(ptr).map(|t| &t.token) == Some(&Token::Star) {
            if let Some(attr) = attrs.first() {
                return Err(ParseError::new(
                    "derive is only supported for sum type declarations",
                    attr_error_span(attr),
                ));
            }
            ptr += 1;
            return Ok((
                ptr,
                Stmt::Type(TypeDef {
                    span: consumed_span(tokens, ptr),
                    name,
                    name_span,
                    params,
                    variants: vec![],
                    derives,
                }),
            ));
        }

        let alias_shaped_rhs = match tokens.get(ptr).map(|tok| &tok.token) {
            Some(Token::Hash | Token::LParen | Token::Fn | Token::LBracket) => true,
            Some(Token::Ident(id)) if id.starts_with('\'') => true,
            _ => false,
        };
        if alias_shaped_rhs {
            return Err(ParseError::new(
                "type aliases must use `type alias Name = ...`",
                tokens.get(ptr).map(|t| t.span).unwrap_or(Span {
                    line: 0,
                    col: 0,
                    len: 0,
                }),
            ));
        }

        let mut variants = Vec::new();
        loop {
            let variant_start = ptr;
            let (c_vname, vname, vname_span) = self.expect_ident_with_span(&tokens[ptr..])?;
            ptr += c_vname;
            let payload = if tokens.get(ptr).map(|t| &t.token) == Some(&Token::LParen) {
                ptr += 1;
                let (c_ty, ty) = self.parse_type(&tokens[ptr..])?;
                ptr += c_ty;
                ptr += self.expect(&tokens[ptr..], Token::RParen)?;
                Some(ty)
            } else {
                None
            };
            variants.push(Variant {
                span: consumed_span(&tokens[variant_start..], ptr - variant_start),
                name: vname,
                name_span: vname_span,
                payload,
            });
            if tokens.get(ptr).map(|t| &t.token) == Some(&Token::Pipe) {
                ptr += 1;
            } else {
                break;
            }
        }
        Ok((
            ptr,
            Stmt::Type(TypeDef {
                span: consumed_span(tokens, ptr),
                name,
                name_span,
                params,
                variants,
                derives,
            }),
        ))
    }

    fn parse_type_alias_after_keyword(
        &self,
        tokens: &[Spanned],
    ) -> Result<(usize, Stmt), ParseError> {
        let mut ptr = 0;
        let (c_name, name, name_span) = self.expect_ident_with_span(&tokens[ptr..])?;
        ptr += c_name;

        let (consumed_params, params) = self.parse_type_params(&tokens[ptr..])?;
        ptr += consumed_params;

        let equal_span = tokens.get(ptr).map(|tok| tok.span);
        ptr += self.expect(&tokens[ptr..], Token::Equal)?;
        self.reject_missing_rhs_before_next_statement(
            tokens,
            ptr,
            equal_span,
            "expected type after `=` in type alias",
        )?;
        let (c_ty, ty) = self.parse_type(&tokens[ptr..])?;
        ptr += c_ty;
        Ok((
            ptr,
            Stmt::TypeAlias {
                span: consumed_span(tokens, ptr),
                name,
                name_span,
                params,
                ty,
            },
        ))
    }

    fn parse_type_params(&self, tokens: &[Spanned]) -> Result<(usize, Vec<String>), ParseError> {
        let mut ptr = 0;
        let mut params = Vec::new();
        if tokens.get(ptr).map(|t| &t.token) != Some(&Token::LParen) {
            return Ok((0, params));
        }

        ptr += 1;
        loop {
            let (consumed_param, param) = self.expect_ident(&tokens[ptr..])?;
            ptr += consumed_param;
            params.push(param);
            if tokens.get(ptr).map(|t| &t.token) == Some(&Token::Comma) {
                ptr += 1;
            } else {
                break;
            }
        }
        ptr += self.expect(&tokens[ptr..], Token::RParen)?;
        Ok((ptr, params))
    }

    fn reject_missing_rhs_before_next_statement(
        &self,
        tokens: &[Spanned],
        ptr: usize,
        equal_span: Option<Span>,
        message: &str,
    ) -> Result<(), ParseError> {
        let Some(next) = tokens.get(ptr) else {
            return Ok(());
        };
        if matches!(next.token, Token::Eof)
            || equal_span.is_some_and(|span| {
                next.span.line > span.line && starts_statement_or_item(&next.token)
            })
        {
            return Err(ParseError::new(message, next.span));
        }
        Ok(())
    }

    fn parse_derive_attrs(&self, attrs: &[Attribute]) -> Result<Vec<DeriveAttr>, ParseError> {
        let mut derives = Vec::new();
        let mut seen = Vec::new();
        for attr in attrs {
            if !attr.is("derive") {
                return Err(ParseError::new(
                    format!("Unknown attribute `{}`", attr.name),
                    attr_error_span(attr),
                ));
            }
            if attr.args.is_empty() {
                return Err(ParseError::new(
                    "Attribute `derive` requires at least one argument",
                    attr_error_span(attr),
                ));
            }
            let mut traits = Vec::new();
            for arg in &attr.args {
                let derive_trait = match arg.as_str() {
                    "Eq" => DeriveTrait::Eq,
                    "ToString" => DeriveTrait::ToString,
                    _ => {
                        return Err(ParseError::new(
                            format!(
                                "Cannot derive `{}`: supported derives are Eq, ToString",
                                arg
                            ),
                            attr_error_span(attr),
                        ));
                    }
                };
                if seen.contains(&derive_trait) {
                    return Err(ParseError::new(
                        format!("Duplicate derive `{}`", derive_trait.name()),
                        attr_error_span(attr),
                    ));
                }
                seen.push(derive_trait);
                traits.push(derive_trait);
            }
            derives.push(DeriveAttr {
                traits,
                span: attr.span,
            });
        }
        Ok(derives)
    }

    fn parse_trait_stmt(&self, tokens: &[Spanned]) -> Result<(usize, Stmt), ParseError> {
        let mut ptr = 0;
        ptr += self.expect(&tokens[ptr..], Token::Trait)?;
        let (c_name, name, name_span) = self.expect_ident_with_span(&tokens[ptr..])?;
        ptr += c_name;
        let mut params = Vec::new();
        let mut determinant_len = None;
        while tokens.get(ptr).map(|t| &t.token) != Some(&Token::LBrace) {
            if tokens.get(ptr).map(|t| &t.token) == Some(&Token::Arrow) {
                if params.is_empty() {
                    return Err(ParseError::new(
                        "Expected at least one determinant trait parameter before `->`",
                        tokens[ptr].span,
                    ));
                }
                if determinant_len.is_some() {
                    return Err(ParseError::new(
                        "Expected only one functional dependency arrow in trait head",
                        tokens[ptr].span,
                    ));
                }
                determinant_len = Some(params.len());
                ptr += 1;
                continue;
            }
            let (c_param, param) = self.expect_ident(&tokens[ptr..])?;
            ptr += c_param;
            if params.contains(&param) {
                return Err(ParseError::new(
                    format!("Duplicate trait parameter `{}`", param),
                    tokens[ptr - c_param].span,
                ));
            }
            params.push(param);
        }
        if params.is_empty() {
            return Err(ParseError::new(
                "Expected at least one trait parameter",
                tokens[ptr].span,
            ));
        }
        let fundeps = if let Some(det_len) = determinant_len {
            if det_len == params.len() {
                return Err(ParseError::new(
                    "Expected at least one dependent trait parameter after `->`",
                    tokens[ptr].span,
                ));
            }
            vec![FunctionalDependency {
                determinants: (0..det_len).collect(),
                dependents: (det_len..params.len()).collect(),
            }]
        } else {
            vec![]
        };
        ptr += self.expect(&tokens[ptr..], Token::LBrace)?;
        let mut methods = Vec::new();
        while tokens.get(ptr).map(|t| &t.token) != Some(&Token::RBrace) {
            let method_start = ptr;
            let (c_attrs, inline) = self.parse_inline_attrs(tokens, ptr)?;
            ptr += c_attrs;
            ptr += self.expect(&tokens[ptr..], Token::Fn)?;
            let fixity = if let Some(Token::Ident(s)) = tokens.get(ptr).map(|t| &t.token)
                && (s == "infixl" || s == "infixr" || s == "infix")
            {
                let f = match s.as_str() {
                    "infixl" => Fixity::Left,
                    "infixr" => Fixity::Right,
                    _ => Fixity::Non,
                };
                ptr += 1;
                let prec_tok = tokens.get(ptr).ok_or_else(|| {
                    ParseError::new(
                        "Expected precedence",
                        Span {
                            line: 0,
                            col: 0,
                            len: 0,
                        },
                    )
                })?;
                let p = if let Token::Number(n) = &prec_tok.token {
                    n.precedence_value()
                } else {
                    return Err(ParseError::new("Expected precedence number", prec_tok.span));
                };
                ptr += 1;
                Some((f, p))
            } else {
                None
            };
            let (c_mname, mname, mname_span) = self.expect_name_with_span(&tokens[ptr..])?;
            ptr += c_mname;
            ptr += self.expect(&tokens[ptr..], Token::LParen)?;
            let mut params = Vec::new();
            if tokens.get(ptr).map(|t| &t.token) != Some(&Token::RParen) {
                loop {
                    let (c_pname, pname) = self.expect_ident(&tokens[ptr..])?;
                    ptr += c_pname;
                    ptr += self.expect(&tokens[ptr..], Token::Colon)?;
                    let (c_ty, ty) = self.parse_type(&tokens[ptr..])?;
                    ptr += c_ty;
                    params.push((pname, ty));
                    if tokens.get(ptr).map(|t| &t.token) == Some(&Token::Comma) {
                        ptr += 1;
                    } else {
                        break;
                    }
                }
            }
            ptr += self.expect(&tokens[ptr..], Token::RParen)?;
            ptr += self.expect(&tokens[ptr..], Token::Arrow)?;
            let (c_ret, ret_type) = self.parse_type(&tokens[ptr..])?;
            ptr += c_ret;
            methods.push(TraitMethod {
                span: consumed_span(&tokens[method_start..], ptr - method_start),
                name: mname,
                name_span: mname_span,
                fixity,
                params,
                ret_type,
                inline,
            });
        }
        ptr += self.expect(&tokens[ptr..], Token::RBrace)?;
        Ok((
            ptr,
            #[allow(deprecated)]
            Stmt::Trait(TraitDef {
                span: consumed_span(tokens, ptr),
                name,
                name_span,
                param: params[0].clone(),
                params,
                fundeps,
                methods,
            }),
        ))
    }

    fn parse_impl_stmt(&self, tokens: &[Spanned]) -> Result<(usize, Stmt), ParseError> {
        let mut ptr = 0;
        ptr += self.expect(&tokens[ptr..], Token::Impl)?;
        let (c_head, head) = self.parse_type(&tokens[ptr..])?;
        ptr += c_head;
        if tokens.get(ptr).map(|t| &t.token) != Some(&Token::For) {
            return self.parse_inherent_impl_tail(tokens, ptr, head);
        }
        let Type::Ident(trait_name) = head else {
            return Err(ParseError::new(
                "Expected trait name before `for` in trait impl",
                tokens[0].span,
            ));
        };
        ptr += self.expect(&tokens[ptr..], Token::For)?;
        let (c_trait_args, trait_args, fundep_arrow_index) =
            self.parse_impl_trait_args(&tokens[ptr..])?;
        ptr += c_trait_args;
        let (c_bounds, type_bounds) = self.parse_where_type_bounds(&tokens[ptr..])?;
        ptr += c_bounds;
        ptr += self.expect(&tokens[ptr..], Token::LBrace)?;
        let mut methods = Vec::new();
        while tokens.get(ptr).map(|t| &t.token) != Some(&Token::RBrace) {
            let method_start = ptr;
            let (c_attrs, inline) = self.parse_inline_attrs(tokens, ptr)?;
            ptr += c_attrs;
            ptr += self.expect(&tokens[ptr..], Token::Fn)?;
            let (c_mname, mname, mname_span) = self.expect_name_with_span(&tokens[ptr..])?;
            ptr += c_mname;
            ptr += self.expect(&tokens[ptr..], Token::LParen)?;
            let mut params = Vec::new();
            if tokens.get(ptr).map(|t| &t.token) != Some(&Token::RParen) {
                loop {
                    let (consumed, param) = self.parse_param(&tokens[ptr..], false)?;
                    ptr += consumed;
                    params.push(param);
                    if tokens.get(ptr).map(|t| &t.token) == Some(&Token::Comma) {
                        ptr += 1;
                    } else {
                        break;
                    }
                }
            }
            ptr += self.expect(&tokens[ptr..], Token::RParen)?;

            let mut ret_type = None;
            if tokens.get(ptr).map(|t| &t.token) == Some(&Token::Arrow) {
                ptr += 1;
                let (c_ret, parsed_ret) = self.parse_type(&tokens[ptr..])?;
                ptr += c_ret;
                ret_type = Some(TypeReturn::value(parsed_ret));
            }

            let (c_body, body) = self.parse_expr(&tokens[ptr..], 0)?;
            ptr += c_body;
            methods.push(ImplMethod {
                span: consumed_span(&tokens[method_start..], ptr - method_start),
                name: mname,
                name_span: mname_span,
                params,
                ret_type,
                body,
                inline,
            });
        }
        ptr += self.expect(&tokens[ptr..], Token::RBrace)?;
        Ok((
            ptr,
            #[allow(deprecated)]
            Stmt::Impl(ImplDef {
                span: consumed_span(tokens, ptr),
                trait_name,
                target: trait_args[0].clone(),
                trait_args,
                dict_arg_indexes: vec![],
                used_fundep_arrow: fundep_arrow_index.is_some(),
                fundep_arrow_index,
                type_bounds,
                dict_params: vec![],
                methods,
                generated_by: None,
            }),
        ))
    }

    fn parse_impl_trait_args(
        &self,
        tokens: &[Spanned],
    ) -> Result<(usize, Vec<Type>, Option<usize>), ParseError> {
        let mut ptr = 0;
        let mut args = Vec::new();
        let mut fundep_arrow_index = None;
        loop {
            let (consumed, ty) = self.parse_type(&tokens[ptr..])?;
            ptr += consumed;
            args.push(ty);
            match tokens.get(ptr).map(|t| &t.token) {
                Some(Token::Comma) => ptr += 1,
                Some(Token::Arrow) => {
                    if fundep_arrow_index.is_some() {
                        return Err(ParseError::new(
                            "Expected only one `->` in impl target",
                            tokens[ptr].span,
                        ));
                    }
                    fundep_arrow_index = Some(args.len());
                    ptr += 1;
                }
                _ => break,
            }
        }
        Ok((ptr, args, fundep_arrow_index))
    }

    fn parse_inherent_impl_tail(
        &self,
        tokens: &[Spanned],
        mut ptr: usize,
        target: Type,
    ) -> Result<(usize, Stmt), ParseError> {
        let (c_bounds, type_bounds) = self.parse_where_type_bounds(&tokens[ptr..])?;
        ptr += c_bounds;
        ptr += self.expect(&tokens[ptr..], Token::LBrace)?;
        let mut methods = Vec::new();
        while tokens.get(ptr).map(|t| &t.token) != Some(&Token::RBrace) {
            let method_start = ptr;
            ptr += self.expect(&tokens[ptr..], Token::Fn)?;
            let (c_mname, mname, mname_span) = self.expect_ident_with_span(&tokens[ptr..])?;
            ptr += c_mname;
            let (c_tail, params, ret_type, type_bounds, body) =
                self.parse_fn_params_body(&tokens[ptr..])?;
            ptr += c_tail;
            methods.push(InherentMethod {
                span: consumed_span(&tokens[method_start..], ptr - method_start),
                name: mname,
                name_span: mname_span,
                params,
                ret_type,
                body,
                dict_params: vec![],
                type_bounds,
            });
        }
        ptr += self.expect(&tokens[ptr..], Token::RBrace)?;
        Ok((
            ptr,
            Stmt::InherentImpl(InherentImplDef {
                span: consumed_span(tokens, ptr),
                target,
                type_bounds,
                methods,
            }),
        ))
    }

    fn parse_extern_stmt(&self, tokens: &[Spanned]) -> Result<(usize, Stmt), ParseError> {
        let mut ptr = 0;
        ptr += self.expect(&tokens[ptr..], Token::Extern)?;
        let (c_name, name, name_span) = self.expect_ident_with_span(&tokens[ptr..])?;
        ptr += c_name;
        ptr += self.expect(&tokens[ptr..], Token::Colon)?;
        let (c_ty, ty) = self.parse_type(&tokens[ptr..])?;
        ptr += c_ty;
        ptr += self.expect(&tokens[ptr..], Token::Equal)?;
        let (c_marker, is_template) = self.parse_extern_kind_marker(tokens, ptr)?;
        ptr += c_marker;

        let tok = tokens.get(ptr).ok_or_else(|| {
            ParseError::new(
                "Expected string literal",
                Span {
                    line: 0,
                    col: 0,
                    len: 0,
                },
            )
        })?;
        let lib_path = if let Token::StringLit(s) = &tok.token {
            s.clone()
        } else {
            return Err(ParseError::new(
                format!("Expected string literal, found {}", tok.token),
                tok.span,
            ));
        };
        ptr += 1;
        ptr += self.expect(&tokens[ptr..], Token::Semicolon)?;

        let kind = if is_template {
            ExternKind::Template(lib_path)
        } else {
            ExternKind::Value(lib_path)
        };

        Ok((
            ptr,
            Stmt::Extern {
                span: consumed_span(tokens, ptr),
                name,
                name_span,
                ty,
                kind,
            },
        ))
    }

    fn parse_for_pattern(&self, tokens: &[Spanned]) -> Result<(usize, Pattern), ParseError> {
        if let Some(Token::Ident(name)) = tokens.first().map(|t| &t.token) {
            let is_simple = name != "_"
                && name
                    .chars()
                    .next()
                    .map(|c| c.is_lowercase())
                    .unwrap_or(false)
                && tokens.get(1).map(|t| &t.token) != Some(&Token::LParen);
            if is_simple {
                let span = SourceSpan::from_lex_span(tokens[0].span);
                return Ok((1, Pattern::Variable(name.clone(), span)));
            }
        }
        if let Some(Token::Ident(name)) = tokens.first().map(|t| &t.token)
            && name == "_"
        {
            return Ok((1, Pattern::Wildcard));
        }
        self.parse_pattern(tokens)
    }

    fn parse_for_expr(&self, tokens: &[Spanned]) -> Result<(usize, Expr), ParseError> {
        let mut ptr = 0;
        ptr += self.expect(&tokens[ptr..], Token::For)?;
        let (c_pat, pat) = self.parse_for_pattern(&tokens[ptr..])?;
        ptr += c_pat;
        ptr += self.expect(&tokens[ptr..], Token::In)?;
        let (c_iter, iterable) = self.parse_expr(&tokens[ptr..], 0)?;
        ptr += c_iter;
        let (c_body, body) = self.parse_block(&tokens[ptr..])?;
        ptr += c_body;
        Ok((
            ptr,
            self.expr_from_tokens(
                tokens,
                ptr,
                ExprKind::For {
                    pat,
                    iterable: Box::new(iterable),
                    body: Box::new(body),
                    resolved_iter: None,
                    pending_iter: None,
                },
            ),
        ))
    }

    fn parse_loop_expr(&self, tokens: &[Spanned]) -> Result<(usize, Expr), ParseError> {
        let mut ptr = 0;
        ptr += self.expect(&tokens[ptr..], Token::Loop)?;
        let (c_body, body) = self.parse_block(&tokens[ptr..])?;
        ptr += c_body;
        Ok((
            ptr,
            self.expr_from_tokens(tokens, ptr, ExprKind::Loop(Box::new(body))),
        ))
    }

    fn parse_break_expr(&self, tokens: &[Spanned]) -> Result<(usize, Expr), ParseError> {
        let mut ptr = 0;
        ptr += self.expect(&tokens[ptr..], Token::Break)?;
        let mut value = None;
        if let Some(next) = tokens.get(ptr) {
            match next.token {
                Token::Semicolon
                | Token::RBrace
                | Token::Comma
                | Token::RParen
                | Token::RBracket => {}
                _ => {
                    let (c_expr, expr) = self.parse_expr(&tokens[ptr..], 0)?;
                    ptr += c_expr;
                    value = Some(Box::new(expr));
                }
            }
        }
        Ok((
            ptr,
            self.expr_from_tokens(tokens, ptr, ExprKind::Break(value)),
        ))
    }

    fn parse_return_expr(&self, tokens: &[Spanned]) -> Result<(usize, Expr), ParseError> {
        let mut ptr = 0;
        ptr += self.expect(&tokens[ptr..], Token::Return)?;
        let mut value = None;
        if let Some(next) = tokens.get(ptr) {
            match next.token {
                Token::Semicolon
                | Token::RBrace
                | Token::Comma
                | Token::RParen
                | Token::RBracket => {}
                _ => {
                    let (c_expr, expr) = self.parse_expr(&tokens[ptr..], 0)?;
                    ptr += c_expr;
                    value = Some(Box::new(expr));
                }
            }
        }
        Ok((
            ptr,
            self.expr_from_tokens(tokens, ptr, ExprKind::Return(value)),
        ))
    }

    fn parse_match_expr(&self, tokens: &[Spanned]) -> Result<(usize, Expr), ParseError> {
        let mut ptr = 0;
        ptr += self.expect(&tokens[ptr..], Token::Match)?;
        let (c_s, scrutinee) = self.parse_expr(&tokens[ptr..], 0)?;
        ptr += c_s;
        ptr += self.expect(&tokens[ptr..], Token::LBrace)?;
        let mut arms = Vec::new();
        while tokens.get(ptr).map(|t| &t.token) != Some(&Token::RBrace) {
            let (c_pat, pattern) = self.parse_for_pattern(&tokens[ptr..])?;
            ptr += c_pat;
            ptr += self.expect(&tokens[ptr..], Token::Arrow)?;
            let (c_expr, arm_expr) = self.parse_expr(&tokens[ptr..], 0)?;
            ptr += c_expr;
            arms.push((pattern, arm_expr));
            if tokens.get(ptr).map(|t| &t.token) == Some(&Token::Comma) {
                ptr += 1;
            } else {
                break;
            }
        }
        ptr += self.expect(&tokens[ptr..], Token::RBrace)?;
        Ok((
            ptr,
            self.expr_from_tokens(
                tokens,
                ptr,
                ExprKind::Match {
                    scrutinee: Box::new(scrutinee),
                    arms,
                },
            ),
        ))
    }

    fn parse_pattern(&self, tokens: &[Spanned]) -> Result<(usize, Pattern), ParseError> {
        let mut ptr = 0;
        let tok = tokens.first().ok_or_else(|| {
            ParseError::new(
                "Expected pattern",
                Span {
                    line: 0,
                    col: 0,
                    len: 0,
                },
            )
        })?;
        match &tok.token {
            Token::Ident(name) if name == "_" => Ok((1, Pattern::Wildcard)),
            Token::StringLit(s) => Ok((1, Pattern::StringLit(s.clone()))),
            Token::Number(n) => self.parse_number_pattern(tokens, 1, n.clone(), tok.span),
            Token::Minus => {
                let Some(next) = tokens.get(1) else {
                    return Err(ParseError::new(
                        "Expected number after `-` in pattern",
                        tok.span,
                    ));
                };
                let Token::Number(n) = &next.token else {
                    return Err(ParseError::new(
                        "Expected number after `-` in pattern",
                        tok.span,
                    ));
                };
                self.parse_number_pattern(tokens, 2, negate_number_literal(n), tok.span)
            }
            Token::True => Ok((1, Pattern::BoolLit(true))),
            Token::False => Ok((1, Pattern::BoolLit(false))),
            Token::Ident(name) => {
                let name = name.clone();
                ptr += 1;
                let binding = if tokens.get(ptr).map(|t| &t.token) == Some(&Token::LParen) {
                    ptr += 1;
                    let (c_bind, bind_pat) = self.parse_for_pattern(&tokens[ptr..])?;
                    ptr += c_bind;
                    ptr += self.expect(&tokens[ptr..], Token::RParen)?;
                    Some(Box::new(bind_pat))
                } else {
                    None
                };
                Ok((ptr, Pattern::Constructor { name, binding }))
            }
            Token::Hash => {
                ptr += 1;
                ptr += self.expect(&tokens[ptr..], Token::LBrace)?;
                let mut fields: Vec<(String, String, SourceSpan)> = Vec::new();
                let mut rest = None;
                while tokens.get(ptr).map(|t| &t.token) != Some(&Token::RBrace) {
                    if tokens.get(ptr).map(|t| &t.token) == Some(&Token::DotDot) {
                        ptr += 1;
                        rest = if let Some(Token::Ident(n)) = tokens.get(ptr).map(|t| &t.token) {
                            let n = n.clone();
                            let span = SourceSpan::from_lex_span(tokens[ptr].span);
                            ptr += 1;
                            Some(Some((n, span)))
                        } else {
                            Some(None)
                        };
                        break;
                    }
                    let (c_f, field_name, field_span) =
                        self.expect_ident_with_span(&tokens[ptr..])?;
                    ptr += c_f;
                    let (binding_name, binding_span) =
                        if tokens.get(ptr).map(|t| &t.token) == Some(&Token::Colon) {
                            ptr += 1;
                            let (c_b, b, b_span) = self.expect_ident_with_span(&tokens[ptr..])?;
                            ptr += c_b;
                            (b, b_span)
                        } else {
                            (field_name.clone(), field_span)
                        };
                    fields.push((field_name, binding_name, binding_span));
                    if tokens.get(ptr).map(|t| &t.token) == Some(&Token::Comma) {
                        ptr += 1;
                    } else {
                        break;
                    }
                }
                ptr += self.expect(&tokens[ptr..], Token::RBrace)?;
                Ok((ptr, Pattern::Record { fields, rest }))
            }
            Token::LParen => {
                ptr += 1;
                // Parse comma-separated sub-patterns.
                let mut elems: Vec<Pattern> = Vec::new();
                while tokens.get(ptr).map(|t| &t.token) != Some(&Token::RParen) {
                    let (c, sub) = self.parse_for_pattern(&tokens[ptr..])?;
                    ptr += c;
                    elems.push(sub);
                    if tokens.get(ptr).map(|t| &t.token) == Some(&Token::Comma) {
                        ptr += 1;
                    } else {
                        break;
                    }
                }
                ptr += self.expect(&tokens[ptr..], Token::RParen)?;
                // A single element with no trailing comma is just parenthesised — unwrap it.
                if elems.len() == 1 {
                    Ok((ptr, elems.remove(0)))
                } else {
                    Ok((ptr, Pattern::Tuple(elems)))
                }
            }
            Token::LBracket => {
                ptr += 1;
                let mut elements: Vec<Pattern> = Vec::new();
                let mut rest = None;
                while tokens.get(ptr).map(|t| &t.token) != Some(&Token::RBracket) {
                    if tokens.get(ptr).map(|t| &t.token) == Some(&Token::DotDot) {
                        ptr += 1;
                        rest = if let Some(Token::Ident(n)) = tokens.get(ptr).map(|t| &t.token) {
                            let n = n.clone();
                            let span = SourceSpan::from_lex_span(tokens[ptr].span);
                            ptr += 1;
                            Some(Some((n, span)))
                        } else {
                            Some(None)
                        };
                        break;
                    }
                    let (c_e, elem) = self.parse_for_pattern(&tokens[ptr..])?;
                    ptr += c_e;
                    elements.push(elem);
                    if tokens.get(ptr).map(|t| &t.token) == Some(&Token::Comma) {
                        ptr += 1;
                    } else {
                        break;
                    }
                }
                ptr += self.expect(&tokens[ptr..], Token::RBracket)?;
                Ok((ptr, Pattern::List { elements, rest }))
            }
            _ => Err(ParseError::new(
                format!("Expected pattern, found {}", tok.token),
                tok.span,
            )),
        }
    }

    fn parse_number_pattern(
        &self,
        tokens: &[Spanned],
        mut ptr: usize,
        number: NumberLiteral,
        number_span: Span,
    ) -> Result<(usize, Pattern), ParseError> {
        if !matches!(
            tokens.get(ptr).map(|t| &t.token),
            Some(Token::DotDot | Token::DotDotEq)
        ) {
            return Ok((ptr, Pattern::NumberLit(number)));
        }

        let NumberLiteral::Int(start) = number else {
            return Err(ParseError::new(
                "range patterns require integer bounds",
                number_span,
            ));
        };
        let op_tok = &tokens[ptr];
        let inclusive = op_tok.token == Token::DotDotEq;
        ptr += 1;
        let (consumed_end, end) = parse_signed_int_pattern_bound(&tokens[ptr..], op_tok.span)?;
        ptr += consumed_end;
        Ok((
            ptr,
            Pattern::IntRange {
                start,
                end,
                inclusive,
            },
        ))
    }

    fn parse_type(&self, tokens: &[Spanned]) -> Result<(usize, Type), ParseError> {
        let mut ptr = 0;
        let tok = tokens.get(ptr).ok_or_else(|| {
            ParseError::new(
                "Unexpected EOF",
                Span {
                    line: 0,
                    col: 0,
                    len: 0,
                },
            )
        })?;

        let mut base = match &tok.token {
            Token::Star => {
                ptr += 1;
                Type::Hole
            }
            Token::Bang => {
                ptr += 1;
                Type::Never
            }
            Token::Fn => {
                ptr += 1;
                ptr += self.expect(&tokens[ptr..], Token::LParen)?;
                let mut param_types = Vec::new();
                if tokens.get(ptr).map(|t| &t.token) != Some(&Token::RParen) {
                    loop {
                        let mut mut_place = false;
                        if tokens.get(ptr).map(|t| &t.token) == Some(&Token::Mut) {
                            mut_place = true;
                            ptr += 1;
                        }
                        let (c_ty, ty) = self.parse_type(&tokens[ptr..])?;
                        ptr += c_ty;
                        param_types.push(if mut_place {
                            TypeParam::mut_place(ty)
                        } else {
                            TypeParam::value(ty)
                        });
                        if tokens.get(ptr).map(|t| &t.token) == Some(&Token::Comma) {
                            ptr += 1;
                        } else {
                            break;
                        }
                    }
                }
                ptr += self.expect(&tokens[ptr..], Token::RParen)?;
                ptr += self.expect(&tokens[ptr..], Token::Arrow)?;
                let mut ret_mut_place = false;
                if tokens.get(ptr).map(|t| &t.token) == Some(&Token::Mut) {
                    ret_mut_place = true;
                    ptr += 1;
                }
                let (c_ret, ret) = self.parse_type(&tokens[ptr..])?;
                ptr += c_ret;
                Type::Func(
                    param_types,
                    if ret_mut_place {
                        TypeReturn::mut_place(ret)
                    } else {
                        TypeReturn::value(ret)
                    },
                )
            }
            Token::Ident(name) => {
                ptr += 1;
                if name.starts_with('\'') {
                    Type::Var(name.clone())
                } else {
                    Type::Ident(name.clone())
                }
            }
            Token::LParen => {
                ptr += 1;
                if tokens.get(ptr).map(|t| &t.token) == Some(&Token::RParen) {
                    ptr += 1;
                    Type::Unit
                } else {
                    let mut types = Vec::new();
                    loop {
                        let (consumed, ty) = self.parse_type(&tokens[ptr..])?;
                        ptr += consumed;
                        types.push(ty);
                        if tokens.get(ptr).map(|t| &t.token) == Some(&Token::Comma) {
                            ptr += 1;
                            if tokens.get(ptr).map(|t| &t.token) == Some(&Token::RParen) {
                                break;
                            }
                        } else {
                            break;
                        }
                    }
                    ptr += self.expect(&tokens[ptr..], Token::RParen)?;
                    if types.len() == 1 {
                        types.pop().unwrap() // len == 1 checked above
                    } else {
                        Type::Tuple(types)
                    }
                }
            }
            Token::LBracket => {
                ptr += 1;
                let (consumed, ty) = self.parse_type(&tokens[ptr..])?;
                ptr += consumed;
                ptr += self.expect(&tokens[ptr..], Token::RBracket)?;
                // [T] -> Array[T]
                Type::App(Box::new(Type::Ident("Array".to_string())), vec![ty])
            }
            Token::Hash => {
                ptr += 1;
                ptr += self.expect(&tokens[ptr..], Token::LBrace)?;
                let mut fields = Vec::new();
                let mut is_open = false;
                if tokens.get(ptr).map(|t| &t.token) != Some(&Token::RBrace) {
                    loop {
                        if tokens.get(ptr).map(|t| &t.token) == Some(&Token::DotDot) {
                            is_open = true;
                            ptr += 1;
                            break;
                        }
                        let (c_name, name) = self.expect_ident(&tokens[ptr..])?;
                        ptr += c_name;
                        ptr += self.expect(&tokens[ptr..], Token::Colon)?;
                        let (c_ty, ty) = self.parse_type(&tokens[ptr..])?;
                        ptr += c_ty;
                        fields.push((name, ty));
                        if tokens.get(ptr).map(|t| &t.token) == Some(&Token::Comma) {
                            ptr += 1;
                            if tokens.get(ptr).map(|t| &t.token) == Some(&Token::RBrace) {
                                break;
                            }
                        } else {
                            break;
                        }
                    }
                }
                ptr += self.expect(&tokens[ptr..], Token::RBrace)?;
                Type::Record(fields, is_open)
            }
            _ => {
                return Err(ParseError::new(
                    format!("Expected type, found {}", tok.token),
                    tok.span,
                ));
            }
        };

        // Check for type application: Base(Arg1, Arg2)
        if let Some(next) = tokens.get(ptr)
            && next.token == Token::LParen
        {
            ptr += 1;
            let mut args = Vec::new();
            loop {
                let (consumed, arg) = self.parse_type(&tokens[ptr..])?;
                ptr += consumed;
                args.push(arg);
                if tokens.get(ptr).map(|t| &t.token) == Some(&Token::Comma) {
                    ptr += 1;
                } else {
                    break;
                }
            }
            ptr += self.expect(&tokens[ptr..], Token::RParen)?;
            base = Type::App(Box::new(base), args);
        }

        Ok((ptr, base))
    }

    fn parse_expr(&self, tokens: &[Spanned], min_bp: u8) -> Result<(usize, Expr), ParseError> {
        let mut ptr = 0;
        let tok = tokens.get(ptr).ok_or_else(|| {
            ParseError::new(
                "Unexpected EOF",
                Span {
                    line: 0,
                    col: 0,
                    len: 0,
                },
            )
        })?;

        let mut lhs = match &tok.token {
            Token::Number(n) => {
                let n = n.clone();
                ptr += 1;
                self.expr_from_tokens(tokens, ptr, ExprKind::Number(n))
            }
            Token::StringLit(s) => {
                let s = s.clone();
                ptr += 1;
                self.expr_from_tokens(tokens, ptr, ExprKind::StringLit(s))
            }
            Token::True => {
                ptr += 1;
                self.expr_from_tokens(tokens, ptr, ExprKind::Bool(true))
            }
            Token::False => {
                ptr += 1;
                self.expr_from_tokens(tokens, ptr, ExprKind::Bool(false))
            }
            Token::Bang => {
                ptr += 1;
                let (consumed, operand) = self.parse_expr(&tokens[ptr..], 8)?;
                ptr += consumed;
                self.expr_from_tokens(tokens, ptr, ExprKind::Not(Box::new(operand)))
            }
            Token::Minus => {
                ptr += 1;
                let (consumed, operand) = self.parse_expr(&tokens[ptr..], 11)?;
                ptr += consumed;
                let op_span = SourceSpan::from_lex_span(tok.span);
                self.expr_from_tokens(
                    tokens,
                    ptr,
                    ExprKind::Neg {
                        operand: Box::new(operand),
                        op_span,
                        resolved_op: None,
                        pending_op: None,
                    },
                )
            }
            Token::Ident(name) => {
                ptr += 1;
                self.expr_from_tokens(tokens, ptr, ExprKind::Ident(name.clone()))
            }
            Token::LBrace => {
                let (consumed, block) = self.parse_block(tokens)?;
                ptr += consumed;
                block
            }
            Token::LParen => {
                let (consumed, tuple_or_paren) = self.parse_tuple_or_paren(tokens)?;
                ptr += consumed;
                tuple_or_paren
            }
            Token::LBracket => {
                let (consumed, array) = self.parse_array(tokens)?;
                ptr += consumed;
                array
            }
            Token::Hash => {
                let (consumed, record) = self.parse_record(tokens)?;
                ptr += consumed;
                record
            }
            Token::If => {
                let (consumed, if_expr) = self.parse_if(tokens)?;
                ptr += consumed;
                if_expr
            }
            Token::Match => {
                let (consumed, match_expr) = self.parse_match_expr(tokens)?;
                ptr += consumed;
                match_expr
            }
            Token::For => {
                let (consumed, for_expr) = self.parse_for_expr(tokens)?;
                ptr += consumed;
                for_expr
            }
            Token::Loop => {
                let (consumed, loop_expr) = self.parse_loop_expr(tokens)?;
                ptr += consumed;
                loop_expr
            }
            Token::Break => {
                let (consumed, break_expr) = self.parse_break_expr(tokens)?;
                ptr += consumed;
                break_expr
            }
            Token::Continue => {
                ptr += 1;
                self.expr_from_tokens(tokens, ptr, ExprKind::Continue)
            }
            Token::Return => {
                let (consumed, ret_expr) = self.parse_return_expr(tokens)?;
                ptr += consumed;
                ret_expr
            }
            Token::Import => {
                ptr += 1;
                let path_tok = tokens.get(ptr).ok_or_else(|| {
                    ParseError::new(
                        "Expected string literal after import",
                        Span {
                            line: 0,
                            col: 0,
                            len: 0,
                        },
                    )
                })?;
                let Token::StringLit(path) = &path_tok.token else {
                    return Err(ParseError::new(
                        format!(
                            "Expected string literal after import, found {}",
                            path_tok.token
                        ),
                        path_tok.span,
                    ));
                };
                ptr += 1;
                self.expr_from_tokens(tokens, ptr, ExprKind::Import(path.clone()))
            }
            Token::Fn => {
                let (consumed, lambda) = self.parse_lambda(tokens)?;
                ptr += consumed;
                lambda
            }
            Token::DotDot | Token::DotDotEq => {
                let inclusive = tok.token == Token::DotDotEq;
                ptr += 1;
                if inclusive && can_end_range(tokens, ptr) {
                    return Err(ParseError::new("`..=` requires an end bound", tok.span));
                }
                let end = if can_end_range(tokens, ptr) {
                    None
                } else {
                    let (consumed, end) = self.parse_expr(&tokens[ptr..], 3)?;
                    ptr += consumed;
                    Some(Box::new(end))
                };
                self.expr_from_tokens(
                    tokens,
                    ptr,
                    ExprKind::Range {
                        start: None,
                        end,
                        inclusive,
                    },
                )
            }
            Token::Do => {
                let (consumed, do_expr) = self.parse_do_expr(tokens)?;
                ptr += consumed;
                do_expr
            }
            _ => {
                return Err(ParseError::new(
                    format!("Unexpected token in expression: {}", tok.token),
                    tok.span,
                ));
            }
        };

        while let Some(op_tok) = tokens.get(ptr) {
            match &op_tok.token {
                Token::LParen => {
                    let (l_bp, _r_bp) = (13, 14);
                    if l_bp < min_bp {
                        break;
                    }
                    let (consumed_call, call_expr) = self.parse_call(lhs, &tokens[ptr..])?;
                    ptr += consumed_call;
                    lhs = call_expr;
                }
                Token::Dot => {
                    let (l_bp, _r_bp) = (11, 12);
                    if l_bp < min_bp {
                        break;
                    }
                    ptr += 1;
                    let (c_name, field, field_span) =
                        self.expect_ident_with_span(&tokens[ptr..])?;
                    ptr += c_name;
                    lhs = self.expr_from_tokens(
                        tokens,
                        ptr,
                        ExprKind::FieldAccess {
                            expr: Box::new(lhs),
                            field,
                            field_span,
                        },
                    );
                }
                Token::LBracket => {
                    let (l_bp, _r_bp) = (13, 14);
                    if l_bp < min_bp {
                        break;
                    }
                    ptr += 1;
                    let (consumed_key, key) = self.parse_expr(&tokens[ptr..], 0)?;
                    ptr += consumed_key;
                    ptr += self.expect(&tokens[ptr..], Token::RBracket)?;
                    lhs = self.expr_from_tokens(
                        tokens,
                        ptr,
                        ExprKind::Index {
                            receiver: Box::new(lhs),
                            key: Box::new(key),
                            resolved_callee: None,
                            pending_trait_method: None,
                            dict_args: vec![],
                            pending_dict_args: vec![],
                        },
                    );
                }
                Token::ColonColon => {
                    let (l_bp, _r_bp) = (11, 12);
                    if l_bp < min_bp {
                        break;
                    }
                    let target = associated_target_from_expr(&lhs, op_tok.span, false)?;
                    ptr += 1;
                    let (c_name, member, member_span) =
                        self.expect_ident_with_span(&tokens[ptr..])?;
                    ptr += c_name;
                    lhs = self.expr_from_tokens(
                        tokens,
                        ptr,
                        ExprKind::AssociatedAccess {
                            target,
                            target_span: lhs.span,
                            member,
                            member_span,
                            resolution: None,
                        },
                    );
                }
                Token::DotDot | Token::DotDotEq => {
                    let (l_bp, r_bp) = (2, 3);
                    if l_bp < min_bp {
                        break;
                    }
                    if matches!(lhs.kind, ExprKind::Range { .. }) {
                        return Err(ParseError::new(
                            "ranges cannot be chained; add parentheses to disambiguate",
                            op_tok.span,
                        ));
                    }
                    let inclusive = op_tok.token == Token::DotDotEq;
                    ptr += 1;
                    if inclusive && can_end_range(tokens, ptr) {
                        return Err(ParseError::new("`..=` requires an end bound", op_tok.span));
                    }
                    let end = if can_end_range(tokens, ptr) {
                        None
                    } else {
                        let (consumed_rhs, rhs) = self.parse_expr(&tokens[ptr..], r_bp)?;
                        ptr += consumed_rhs;
                        Some(Box::new(rhs))
                    };
                    lhs = self.expr_from_tokens(
                        tokens,
                        ptr,
                        ExprKind::Range {
                            start: Some(Box::new(lhs)),
                            end,
                            inclusive,
                        },
                    );
                }
                _ if let Some((op, l_bp, r_bp)) = infix_binary_op(&op_tok.token) => {
                    if l_bp < min_bp {
                        break;
                    }
                    let op_span = SourceSpan::from_lex_span(op_tok.span);
                    ptr += 1;
                    let (consumed_rhs, rhs) = self.parse_expr(&tokens[ptr..], r_bp)?;
                    ptr += consumed_rhs;
                    lhs = self.expr_from_tokens(
                        tokens,
                        ptr,
                        ExprKind::Binary {
                            lhs: Box::new(lhs),
                            op,
                            op_span,
                            rhs: Box::new(rhs),
                            resolved_op: None,
                            pending_op: None,
                            dict_args: vec![],
                            pending_dict_args: vec![],
                        },
                    );
                }
                Token::Equal => {
                    let (l_bp, r_bp) = (1, 2);
                    if l_bp < min_bp {
                        break;
                    }
                    // Validate lvalue
                    match &lhs.kind {
                        ExprKind::Ident(_) | ExprKind::FieldAccess { .. } => {}
                        _ => return Err(ParseError::new("Invalid assignment target", op_tok.span)),
                    };
                    ptr += 1;
                    let (consumed_rhs, rhs) = self.parse_expr(&tokens[ptr..], r_bp - 1)?;
                    ptr += consumed_rhs;
                    lhs = self.expr_from_tokens(
                        tokens,
                        ptr,
                        ExprKind::Assign {
                            target: Box::new(lhs),
                            value: Box::new(rhs),
                        },
                    );
                }
                _ => break,
            }
        }

        Ok((ptr, lhs))
    }

    fn parse_if(&self, tokens: &[Spanned]) -> Result<(usize, Expr), ParseError> {
        let mut ptr = 0;
        ptr += self.expect(&tokens[ptr..], Token::If)?;
        let (c_cond, cond) = self.parse_expr(&tokens[ptr..], 0)?;
        ptr += c_cond;
        let (c_then, then_branch) = self.parse_expr(&tokens[ptr..], 0)?;
        ptr += c_then;

        let else_branch = if tokens.get(ptr).map(|t| &t.token) == Some(&Token::Else) {
            ptr += 1;
            let (c_else, expr) = self.parse_expr(&tokens[ptr..], 0)?;
            ptr += c_else;
            expr
        } else {
            self.expr_from_bounds(tokens[0].span, tokens[0].span, ExprKind::Unit)
        };

        Ok((
            ptr,
            self.expr_from_tokens(
                tokens,
                ptr,
                ExprKind::If {
                    cond: Box::new(cond),
                    then_branch: Box::new(then_branch),
                    else_branch: Box::new(else_branch),
                },
            ),
        ))
    }

    fn parse_array(&self, tokens: &[Spanned]) -> Result<(usize, Expr), ParseError> {
        let mut ptr = 0;
        ptr += self.expect(&tokens[ptr..], Token::LBracket)?;
        let mut entries = Vec::new();
        if tokens.get(ptr).map(|t| &t.token) != Some(&Token::RBracket) {
            loop {
                let entry = if tokens.get(ptr).map(|t| &t.token) == Some(&Token::DotDot) {
                    ptr += 1;
                    let (consumed, expr) = self.parse_expr(&tokens[ptr..], 0)?;
                    ptr += consumed;
                    ArrayEntry::Spread(expr)
                } else {
                    let (consumed, expr) = self.parse_expr(&tokens[ptr..], 0)?;
                    ptr += consumed;
                    ArrayEntry::Elem(expr)
                };
                entries.push(entry);
                if tokens.get(ptr).map(|t| &t.token) == Some(&Token::Comma) {
                    ptr += 1;
                    if tokens.get(ptr).map(|t| &t.token) == Some(&Token::RBracket) {
                        break;
                    }
                } else {
                    break;
                }
            }
        }
        ptr += self.expect(&tokens[ptr..], Token::RBracket)?;
        Ok((
            ptr,
            self.expr_from_tokens(tokens, ptr, ExprKind::Array(entries)),
        ))
    }

    fn parse_do_expr(&self, tokens: &[Spanned]) -> Result<(usize, Expr), ParseError> {
        let mut ptr = 0;
        ptr += self.expect(&tokens[ptr..], Token::Do)?;
        ptr += self.expect(&tokens[ptr..], Token::LBrace)?;
        let open_brace_span = tokens[ptr - 1].span; // used for EOF error inside the block

        let mut stmts: Vec<DoStmt> = Vec::new();
        let mut final_expr: Option<Expr> = None;

        while tokens.get(ptr).map(|t| &t.token) != Some(&Token::RBrace) {
            let tok = tokens
                .get(ptr)
                .ok_or_else(|| ParseError::new("unexpected end of `do` block", open_brace_span))?;

            if matches!(tok.token, Token::Let) {
                let let_start = ptr;
                ptr += 1; // consume `let`
                let is_mutable = if tokens.get(ptr).map(|t| &t.token) == Some(&Token::Mut) {
                    ptr += 1;
                    true
                } else {
                    false
                };
                let (c_pat, pat) = self.parse_for_pattern(&tokens[ptr..])?;
                ptr += c_pat;

                let mut ty = None;
                if tokens.get(ptr).map(|t| &t.token) == Some(&Token::Colon) {
                    ptr += 1;
                    let (c_ty, parsed_ty) = self.parse_type(&tokens[ptr..])?;
                    ptr += c_ty;
                    ty = Some(parsed_ty);
                }

                if tokens.get(ptr).map(|t| &t.token) == Some(&Token::Equal) {
                    // Plain let: `let [mut] pat [: ty] = expr ;`
                    ptr += 1;
                    let (c_expr, expr) = self.parse_expr(&tokens[ptr..], 0)?;
                    ptr += c_expr;
                    ptr += self.expect(&tokens[ptr..], Token::Semicolon)?;
                    check_do_control_flow(&expr, false)?;
                    let stmt_span = consumed_span(&tokens[let_start..], ptr - let_start);
                    stmts.push(DoStmt::Let(pat, is_mutable, ty, stmt_span, expr));
                } else if matches!(tokens.get(ptr).map(|t| &t.token), Some(Token::Op(op)) if op == "<-")
                {
                    // Monadic bind: `let [mut] pat [: ty] <- expr ;`
                    let arrow_span = SourceSpan::from_lex_span(tokens[ptr].span);
                    ptr += 1;
                    let (c_expr, expr) = self.parse_expr(&tokens[ptr..], 0)?;
                    ptr += c_expr;
                    ptr += self.expect(&tokens[ptr..], Token::Semicolon)?;
                    check_do_control_flow(&expr, false)?;
                    stmts.push(DoStmt::Bind(pat, is_mutable, ty, arrow_span, expr));
                } else {
                    let bad = tokens.get(ptr).map(|t| t.span).unwrap_or(tok.span);
                    return Err(ParseError::new(
                        "expected `=` or `<-` after pattern in `do` block",
                        bad,
                    ));
                }
            } else {
                // Bare expression: either a sequenced statement (`expr ;`) or the final value.
                let (c_expr, expr) = self.parse_expr(&tokens[ptr..], 0)?;
                ptr += c_expr;
                if tokens.get(ptr).map(|t| &t.token) == Some(&Token::Semicolon) {
                    ptr += 1;
                    check_do_control_flow(&expr, false)?;
                    stmts.push(DoStmt::Bare(expr));
                } else {
                    // No semicolon — this is the final expression.
                    check_do_control_flow(&expr, false)?;
                    final_expr = Some(expr);
                    break;
                }
            }
        }

        ptr += self.expect(&tokens[ptr..], Token::RBrace)?;

        let final_expr = final_expr.ok_or_else(|| {
            ParseError::new("`do` block must end with an expression", open_brace_span)
        })?;

        let desugared = self.desugar_do(stmts, final_expr);
        Ok((ptr, desugared))
    }

    /// Right-fold the list of `DoStmt`s into a chain of `>>=` calls.
    ///
    /// `Bind`  → `monad_expr >>= fn(pat) { rest }`
    /// `Let`   → `Block { let pat = value; rest }`
    /// `Bare`  → `expr >>= fn(_) { rest }`
    fn desugar_do(&self, stmts: Vec<DoStmt>, final_expr: Expr) -> Expr {
        stmts
            .into_iter()
            .rev()
            .fold(final_expr, |rest, stmt| match stmt {
                DoStmt::Bind(pat, is_mutable, ty, arrow_span, monad_expr) => {
                    let lambda = Expr::new(
                        self.next_node_id(),
                        SourceSpan::synthetic(),
                        ExprKind::Lambda {
                            params: vec![Param {
                                pat,
                                ty,
                                mut_place: is_mutable,
                            }],
                            return_type: None,
                            body: Box::new(rest),
                            dict_params: vec![],
                        },
                    );
                    Expr::new(
                        self.next_node_id(),
                        SourceSpan::synthetic(),
                        ExprKind::Binary {
                            lhs: Box::new(monad_expr),
                            op: BinOp::Custom(">>=".to_string()),
                            op_span: arrow_span,
                            rhs: Box::new(lambda),
                            resolved_op: None,
                            pending_op: None,
                            dict_args: vec![],
                            pending_dict_args: vec![],
                        },
                    )
                }
                DoStmt::Let(pat, is_mutable, ty, stmt_span, value) => Expr::new(
                    self.next_node_id(),
                    SourceSpan::synthetic(),
                    ExprKind::Block {
                        stmts: vec![Stmt::Let {
                            span: stmt_span,
                            pat,
                            is_mutable,
                            ty,
                            value,
                        }],
                        final_expr: Some(Box::new(rest)),
                    },
                ),
                DoStmt::Bare(expr) => {
                    // No written operator — use the sequenced expression's span as the best
                    // fallback so type-error diagnostics have a location to point to.
                    let op_span = expr.span;
                    let lambda = Expr::new(
                        self.next_node_id(),
                        SourceSpan::synthetic(),
                        ExprKind::Lambda {
                            params: vec![Param {
                                pat: Pattern::Wildcard,
                                ty: None,
                                mut_place: false,
                            }],
                            return_type: None,
                            body: Box::new(rest),
                            dict_params: vec![],
                        },
                    );
                    Expr::new(
                        self.next_node_id(),
                        SourceSpan::synthetic(),
                        ExprKind::Binary {
                            lhs: Box::new(expr),
                            op: BinOp::Custom(">>=".to_string()),
                            op_span,
                            rhs: Box::new(lambda),
                            resolved_op: None,
                            pending_op: None,
                            dict_args: vec![],
                            pending_dict_args: vec![],
                        },
                    )
                }
            })
    }

    fn parse_record(&self, tokens: &[Spanned]) -> Result<(usize, Expr), ParseError> {
        let mut ptr = 0;
        ptr += self.expect(&tokens[ptr..], Token::Hash)?;
        ptr += self.expect(&tokens[ptr..], Token::LBrace)?;
        let mut entries = Vec::new();
        if tokens.get(ptr).map(|t| &t.token) != Some(&Token::RBrace) {
            loop {
                let entry = if tokens.get(ptr).map(|t| &t.token) == Some(&Token::DotDot) {
                    ptr += 1;
                    let (consumed, expr) = self.parse_expr(&tokens[ptr..], 0)?;
                    ptr += consumed;
                    RecordEntry::Spread(expr)
                } else {
                    let (c_name, name) = self.expect_ident(&tokens[ptr..])?;
                    ptr += c_name;
                    if tokens.get(ptr).map(|t| &t.token) == Some(&Token::Colon) {
                        ptr += 1;
                        let (c_expr, expr) = self.parse_expr(&tokens[ptr..], 0)?;
                        ptr += c_expr;
                        RecordEntry::Field(name, expr)
                    } else {
                        let name_span = tokens[ptr - 1].span;
                        let ident_expr = self.expr_from_bounds(
                            name_span,
                            name_span,
                            ExprKind::Ident(name.clone()),
                        );
                        RecordEntry::Field(name, ident_expr)
                    }
                };
                entries.push(entry);
                if tokens.get(ptr).map(|t| &t.token) == Some(&Token::Comma) {
                    ptr += 1;
                    if tokens.get(ptr).map(|t| &t.token) == Some(&Token::RBrace) {
                        break;
                    }
                } else {
                    break;
                }
            }
        }
        ptr += self.expect(&tokens[ptr..], Token::RBrace)?;
        Ok((
            ptr,
            self.expr_from_tokens(tokens, ptr, ExprKind::Record(entries)),
        ))
    }

    fn parse_block(&self, tokens: &[Spanned]) -> Result<(usize, Expr), ParseError> {
        let mut ptr = 0;
        ptr += self.expect(&tokens[ptr..], Token::LBrace)?;
        let mut stmts = Vec::new();
        let mut final_expr = None;
        while ptr < tokens.len() && tokens[ptr].token != Token::RBrace {
            let current_tokens = &tokens[ptr..];
            let first_tok = &current_tokens[0].token;
            let starts_named_fn_stmt = matches!(first_tok, Token::Fn)
                && matches!(
                    current_tokens.get(1).map(|tok| &tok.token),
                    Some(Token::Ident(_))
                );
            if matches!(first_tok, Token::Let) || starts_named_fn_stmt {
                let (consumed, stmt) = self.parse_stmt(current_tokens)?;
                ptr += consumed;
                stmts.push(stmt);
            } else {
                let (consumed_expr, expr) = self.parse_expr(current_tokens, 0)?;
                let next = tokens.get(ptr + consumed_expr).map(|t| &t.token);
                let is_block_like = matches!(
                    &expr.kind,
                    ExprKind::If { .. }
                        | ExprKind::Loop(_)
                        | ExprKind::Match { .. }
                        | ExprKind::Block { .. }
                        | ExprKind::For { .. }
                );
                if next == Some(&Token::Semicolon) {
                    ptr += consumed_expr + 1;
                    stmts.push(Stmt::Expr(expr));
                } else if is_block_like && next != Some(&Token::RBrace) {
                    // Block-like expressions used as statements don't need a semicolon
                    // as long as more tokens follow in this block.
                    ptr += consumed_expr;
                    stmts.push(Stmt::Expr(expr));
                } else if self.recovering && next != Some(&Token::RBrace) && next.is_some() {
                    // In recovery mode, a non-block-like expression not followed by `;` or `}`
                    // is treated as a discarded statement so that parsing can continue. In a
                    // correct program a semicolon is required here, but while the user is
                    // mid-edit we prefer a partial AST over a complete failure.
                    // We still record a diagnostic so the user is informed of the missing `;`.
                    // Point the diagnostic at the end of the expression (zero-width span),
                    // not the start of the next token, so the editor underlines the position
                    // where the `;` is actually missing.
                    let error_span = Span {
                        line: expr.span.end_line,
                        col: expr.span.end_col,
                        len: 0,
                    };
                    self.inner_diagnostics.borrow_mut().push(ParseError::new(
                        "expected `;` after expression statement",
                        error_span,
                    ));
                    ptr += consumed_expr;
                    stmts.push(Stmt::Expr(expr));
                } else {
                    ptr += consumed_expr;
                    final_expr = Some(Box::new(expr));
                    break;
                }
            }
        }
        ptr += self.expect(&tokens[ptr..], Token::RBrace)?;
        Ok((
            ptr,
            self.expr_from_tokens(tokens, ptr, ExprKind::Block { stmts, final_expr }),
        ))
    }

    fn parse_tuple_or_paren(&self, tokens: &[Spanned]) -> Result<(usize, Expr), ParseError> {
        let mut ptr = 0;
        ptr += self.expect(&tokens[ptr..], Token::LParen)?;
        if tokens.get(ptr).map(|t| &t.token) == Some(&Token::RParen) {
            return Ok((
                ptr + 1,
                self.expr_from_tokens(tokens, ptr + 1, ExprKind::Unit),
            ));
        }
        let mut exprs = Vec::new();
        loop {
            let (consumed, expr) = self.parse_expr(&tokens[ptr..], 0)?;
            ptr += consumed;
            exprs.push(expr);
            if tokens.get(ptr).map(|t| &t.token) == Some(&Token::Comma) {
                ptr += 1;
                if tokens.get(ptr).map(|t| &t.token) == Some(&Token::RParen) {
                    break;
                }
            } else {
                break;
            }
        }
        ptr += self.expect(&tokens[ptr..], Token::RParen)?;
        if exprs.len() == 1 && !matches!(tokens.get(ptr - 2).map(|t| &t.token), Some(Token::Comma))
        {
            Ok((
                ptr,
                self.expr_from_tokens(
                    tokens,
                    ptr,
                    ExprKind::Grouped(Box::new(exprs.pop().unwrap())),
                ),
            ))
        } else {
            Ok((
                ptr,
                self.expr_from_tokens(tokens, ptr, ExprKind::Tuple(exprs)),
            ))
        }
    }

    fn parse_call(&self, callee: Expr, tokens: &[Spanned]) -> Result<(usize, Expr), ParseError> {
        let mut ptr = 0;
        ptr += self.expect(&tokens[ptr..], Token::LParen)?;
        let mut args = Vec::new();
        if tokens.get(ptr).map(|t| &t.token) != Some(&Token::RParen) {
            loop {
                let (consumed_arg, arg) = self.parse_expr(&tokens[ptr..], 0)?;
                ptr += consumed_arg;
                args.push(arg);
                if tokens.get(ptr).map(|t| &t.token) == Some(&Token::Comma) {
                    ptr += 1;
                } else {
                    break;
                }
            }
        }
        ptr += self.expect(&tokens[ptr..], Token::RParen)?;
        Ok((
            ptr,
            Expr::new(
                self.next_node_id(),
                SourceSpan {
                    start_line: callee.span.start_line,
                    start_col: callee.span.start_col,
                    end_line: tokens[ptr - 1].span.line,
                    end_col: tokens[ptr - 1].span.col + tokens[ptr - 1].span.len,
                },
                ExprKind::Call {
                    callee: Box::new(callee),
                    args,
                    is_method_call: false,
                    arg_wrappers: Vec::new(),
                    resolved_callee: None,
                    pending_trait_method: None,
                    dict_args: vec![],
                    pending_dict_args: vec![],
                },
            ),
        ))
    }

    fn expect(&self, tokens: &[Spanned], expected: Token) -> Result<usize, ParseError> {
        let tok = tokens.first().ok_or_else(|| {
            ParseError::new(
                "Unexpected EOF",
                Span {
                    line: 0,
                    col: 0,
                    len: 0,
                },
            )
        })?;
        if tok.token == expected {
            Ok(1)
        } else {
            Err(ParseError::new(
                format!("Expected {}, found {}", expected, tok.token),
                tok.span,
            ))
        }
    }

    fn parse_error_span(&self, tokens: &[Spanned], ptr: usize) -> Span {
        tokens
            .get(ptr)
            .or_else(|| ptr.checked_sub(1).and_then(|index| tokens.get(index)))
            .or_else(|| tokens.last())
            .map(|token| token.span)
            .unwrap_or(Span {
                line: 0,
                col: 0,
                len: 0,
            })
    }

    fn parse_lambda(&self, tokens: &[Spanned]) -> Result<(usize, Expr), ParseError> {
        let mut ptr = 0;
        ptr += self.expect(&tokens[ptr..], Token::Fn)?;
        ptr += self.expect(&tokens[ptr..], Token::LParen)?;
        let mut params = Vec::new();
        if tokens.get(ptr).map(|t| &t.token) != Some(&Token::RParen) {
            loop {
                let (consumed, param) = self.parse_param(&tokens[ptr..], true)?;
                ptr += consumed;
                params.push(param);
                if tokens.get(ptr).map(|t| &t.token) == Some(&Token::Comma) {
                    ptr += 1;
                } else {
                    break;
                }
            }
        }
        ptr += self.expect(&tokens[ptr..], Token::RParen)?;
        let return_type = if let Some(tok) = tokens.get(ptr)
            && tok.token == Token::Arrow
        {
            let arrow_span = tok.span;
            ptr += 1;
            let (consumed, ret_ty) = self.parse_type(&tokens[ptr..])?;
            ptr += consumed;
            if tokens.get(ptr).map(|tok| &tok.token) != Some(&Token::LBrace) {
                return Err(ParseError::new(
                    "anonymous functions with return annotations must use `fn(...) -> Type { ... }`",
                    arrow_span,
                ));
            }
            Some(ret_ty)
        } else {
            None
        };
        let (c_body, body) = self.parse_block(&tokens[ptr..])?;
        ptr += c_body;
        Ok((
            ptr,
            self.expr_from_tokens(
                tokens,
                ptr,
                ExprKind::Lambda {
                    params,
                    return_type,
                    body: Box::new(body),
                    dict_params: Vec::new(),
                },
            ),
        ))
    }

    fn expect_ident(&self, tokens: &[Spanned]) -> Result<(usize, String), ParseError> {
        self.expect_ident_with_span(tokens)
            .map(|(consumed, name, _)| (consumed, name))
    }

    fn expect_ident_with_span(
        &self,
        tokens: &[Spanned],
    ) -> Result<(usize, String, SourceSpan), ParseError> {
        let tok = tokens.first().ok_or_else(|| {
            ParseError::new(
                "Unexpected EOF",
                Span {
                    line: 0,
                    col: 0,
                    len: 0,
                },
            )
        })?;
        if let Token::Ident(name) = &tok.token {
            Ok((1, name.clone(), SourceSpan::from_lex_span(tok.span)))
        } else {
            Err(ParseError::new(
                format!("Expected identifier, found {}", tok.token),
                tok.span,
            ))
        }
    }

    fn expect_name_with_span(
        &self,
        tokens: &[Spanned],
    ) -> Result<(usize, String, SourceSpan), ParseError> {
        let tok = tokens.first().ok_or_else(|| {
            ParseError::new(
                "Unexpected EOF",
                Span {
                    line: 0,
                    col: 0,
                    len: 0,
                },
            )
        })?;
        let span = SourceSpan::from_lex_span(tok.span);
        match &tok.token {
            Token::Ident(name) => Ok((1, name.clone(), span)),
            Token::Op(op) => Ok((1, op.clone(), span)),
            Token::Star => Ok((1, "*".to_string(), span)),
            Token::DotDot => Ok((1, "..".to_string(), span)),
            Token::Plus => Ok((1, "+".to_string(), span)),
            Token::Minus => Ok((1, "-".to_string(), span)),
            Token::AmpAmp => Ok((1, "&&".to_string(), span)),
            Token::EqEq => Ok((1, "==".to_string(), span)),
            Token::BangEq => Ok((1, "!=".to_string(), span)),
            Token::PipePipe => Ok((1, "||".to_string(), span)),
            Token::PipeArrow => Ok((1, "|>".to_string(), span)),
            Token::In => Ok((1, "in".to_string(), span)),
            _ => Err(ParseError::new(
                format!("Expected identifier or operator, found {}", tok.token),
                tok.span,
            )),
        }
    }
}
