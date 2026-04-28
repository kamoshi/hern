use crate::ast::*;
use std::collections::HashMap;

// ── Tail-position descriptor ──────────────────────────────────────────────────

/// What to do with the value of an expression at its use site.
#[derive(Copy, Clone)]
enum Tail<'a> {
    /// Emit `return <val>` — function body tail position.
    Return,
    /// Emit `local _ = <val>` — value is discarded (statement position).
    Discard,
    /// Emit `<name> = <val>` — value is captured into a named variable.
    Assign(&'a str),
}

// ── Codegen state ─────────────────────────────────────────────────────────────

pub struct LuaCodegen {
    indent: usize,
    loop_counter: usize,
    current_loop_id: usize,
    current_loop_tmp: String,
    current_break_label: String,
    tmp_counter: usize,
    inline_methods: HashMap<String, InlineMethod>,
    extern_templates: HashMap<String, String>,
    import_mode: ImportMode,
}

#[derive(Clone)]
struct InlineMethod {
    params: Vec<String>,
    body: Expr,
}

#[derive(Clone, Copy)]
pub enum ImportMode {
    Require,
    Bundle,
}

impl Default for LuaCodegen {
    fn default() -> Self {
        Self::new()
    }
}

impl LuaCodegen {
    pub fn new() -> Self {
        Self {
            indent: 0,
            loop_counter: 0,
            current_loop_id: 0,
            current_loop_tmp: String::new(),
            current_break_label: String::new(),
            tmp_counter: 0,
            inline_methods: HashMap::new(),
            extern_templates: HashMap::new(),
            import_mode: ImportMode::Require,
        }
    }

    pub fn with_import_mode(mut self, import_mode: ImportMode) -> Self {
        self.import_mode = import_mode;
        self
    }

    fn ind(&self) -> String {
        " ".repeat(self.indent)
    }

    fn fresh_tmp(&mut self) -> String {
        self.tmp_counter += 1;
        format!("_t_{}", self.tmp_counter)
    }

    // ── Top-level ─────────────────────────────────────────────────────────────
    //
    // Precondition: all `gen_*` methods assume analysis succeeded. Callers must not pass
    // partial or error-bearing programs.

    pub fn gen_program(&mut self, program: &Program) -> String {
        self.collect_codegen_metadata(&[program]);
        self.gen_program_stmts(&program.stmts)
    }

    pub fn gen_program_with_prelude(&mut self, prelude: &Program, program: &Program) -> String {
        self.collect_codegen_metadata(&[prelude, program]);
        self.gen_program_stmts(&program.stmts)
    }

    pub fn gen_module(&mut self, program: &Program) -> String {
        self.gen_module_with_dicts(program, impl_dict_names(program))
    }

    pub fn gen_module_with_dicts(&mut self, program: &Program, dict_names: Vec<String>) -> String {
        self.collect_codegen_metadata(&[program]);
        self.gen_module_stmts(&program.stmts, dict_names)
    }

    pub fn gen_module_with_prelude_and_dicts(
        &mut self,
        prelude: &Program,
        program: &Program,
        dict_names: Vec<String>,
    ) -> String {
        self.collect_codegen_metadata(&[prelude, program]);
        self.gen_module_stmts(&program.stmts, dict_names)
    }

    pub fn gen_prelude_module(&mut self, prelude_stmts: &[Stmt]) -> String {
        let program = Program {
            stmts: prelude_stmts.to_vec(),
        };
        self.collect_codegen_metadata(&[&program]);
        let mut out = String::from("-- Hern generated Lua prelude\n");
        for stmt in prelude_stmts {
            out.push_str(&self.gen_stmt(stmt));
            out.push('\n');
        }
        out.push_str("return {\n");
        self.indent += 2;
        out.push_str(&format!("{}__hern_value = {{\n", self.ind()));
        self.indent += 2;
        for name in prelude_value_names(prelude_stmts) {
            out.push_str(&format!("{}{} = {},\n", self.ind(), name, name));
        }
        self.indent -= 2;
        out.push_str(&format!("{}}},\n", self.ind()));
        out.push_str(&format!("{}__hern_dicts = {{\n", self.ind()));
        self.indent += 2;
        for dict_name in impl_dict_names_from_stmts(prelude_stmts) {
            out.push_str(&format!("{}{} = {},\n", self.ind(), dict_name, dict_name));
        }
        self.indent -= 2;
        out.push_str(&format!("{}}},\n", self.ind()));
        self.indent -= 2;
        out.push_str("}\n");
        out
    }

    pub fn gen_prelude_aliases(prelude_stmts: &[Stmt]) -> String {
        let mut out = String::new();
        for name in prelude_value_names(prelude_stmts) {
            out.push_str(&format!(
                "local {} = __prelude.__hern_value.{}\n",
                name, name
            ));
        }
        for dict_name in impl_dict_names_from_stmts(prelude_stmts) {
            out.push_str(&format!(
                "local {} = __prelude.__hern_dicts.{}\n",
                dict_name, dict_name
            ));
        }
        out
    }

    fn gen_program_stmts(&mut self, stmts: &[Stmt]) -> String {
        let mut out = String::from("-- Hern generated Lua\n");
        for stmt in stmts {
            out.push_str(&self.gen_stmt(stmt));
            out.push('\n');
        }
        out
    }

    fn gen_module_stmts(&mut self, stmts: &[Stmt], dict_names: Vec<String>) -> String {
        let mut out = String::from("-- Hern generated Lua module\n");
        let (body_stmts, final_expr) = split_module_body(stmts);
        for stmt in body_stmts {
            out.push_str(&self.gen_stmt(stmt));
            out.push('\n');
        }

        let mut pre = String::new();
        let value = final_expr
            .map(|expr| self.gen_expr(expr, &mut pre))
            .unwrap_or_else(|| "{}".to_string());
        out.push_str(&pre);
        out.push_str("return {\n");
        self.indent += 2;
        out.push_str(&format!("{}__hern_value = {},\n", self.ind(), value));
        out.push_str(&format!("{}__hern_dicts = {{\n", self.ind()));
        self.indent += 2;
        for dict_name in dict_names {
            out.push_str(&format!("{}{} = {},\n", self.ind(), dict_name, dict_name));
        }
        self.indent -= 2;
        out.push_str(&format!("{}}},\n", self.ind()));
        self.indent -= 2;
        out.push_str("}\n");
        out
    }

    fn collect_codegen_metadata(&mut self, programs: &[&Program]) {
        self.extern_templates.clear();
        self.inline_methods.clear();
        for program in programs {
            self.collect_extern_templates_from_stmts(&program.stmts);
            self.collect_inline_methods_from_stmts(&program.stmts);
        }
    }

    fn collect_extern_templates_from_stmts(&mut self, stmts: &[Stmt]) {
        for stmt in stmts {
            if let Stmt::Extern {
                name,
                kind: ExternKind::Template(template),
                ..
            } = stmt
            {
                self.extern_templates.insert(name.clone(), template.clone());
            }
        }
    }

    fn collect_inline_methods_from_stmts(&mut self, stmts: &[Stmt]) {
        for stmt in stmts {
            let Stmt::Impl(id) = stmt else {
                continue;
            };
            let dict_name = format!("__{}__{}", id.trait_name, impl_target_name(&id.target));
            for method in &id.methods {
                if !method.inline {
                    continue;
                }
                let key = format!("{}.{}", dict_name, mangle_op(&method.name));
                let params = method
                    .params
                    .iter()
                    .filter_map(|(pat, _)| {
                        if let Pattern::Variable(name, _) = pat {
                            Some(name.clone())
                        } else {
                            None
                        }
                    })
                    .collect();
                if method
                    .params
                    .iter()
                    .all(|(pat, _)| matches!(pat, Pattern::Variable(_, _)))
                {
                    self.inline_methods.insert(
                        key,
                        InlineMethod {
                            params,
                            body: method.body.clone(),
                        },
                    );
                }
            }
        }
    }

    // ── Statements ────────────────────────────────────────────────────────────

    fn gen_stmt(&mut self, stmt: &Stmt) -> String {
        match stmt {
            Stmt::Let { pat, value, .. } => {
                let mut pre = String::new();
                let val = self.gen_expr(value, &mut pre);
                match pat {
                    Pattern::Variable(name, _) => {
                        // Simple binding — same as before.
                        if pre.is_empty() {
                            format!("{}local {} = {}", self.ind(), name, val)
                        } else if expr_always_exits(value, true) {
                            format!("{}local {}\n{}", self.ind(), name, pre)
                        } else {
                            format!(
                                "{}local {}\n{}{}{} = {}",
                                self.ind(),
                                name,
                                pre,
                                self.ind(),
                                name,
                                val
                            )
                        }
                    }
                    Pattern::Wildcard => {
                        // Evaluate for side-effects only.
                        if pre.is_empty() {
                            format!("{}local _ = {}", self.ind(), val)
                        } else {
                            pre
                        }
                    }
                    _ => {
                        // Destructuring: store value in a fresh temp, then bind fields.
                        let tmp = self.fresh_tmp();
                        let bindings = self.gen_for_pattern_bindings(pat, &tmp);
                        if pre.is_empty() {
                            format!("{}local {} = {}\n{}", self.ind(), tmp, val, bindings)
                        } else if expr_always_exits(value, true) {
                            format!("{}local {}\n{}", self.ind(), tmp, pre)
                        } else {
                            format!(
                                "{}local {}\n{}{}{} = {}\n{}",
                                self.ind(),
                                tmp,
                                pre,
                                self.ind(),
                                tmp,
                                val,
                                bindings
                            )
                        }
                    }
                }
            }
            Stmt::Fn {
                name,
                params,
                body,
                dict_params,
                ..
            } => self.gen_function(name, params, dict_params, body),
            // Assignment as a statement — avoids the expression-position IIFE.
            Stmt::Expr(Expr {
                kind: ExprKind::Assign { target, value },
                ..
            }) => {
                let mut pre = String::new();
                let t = self.gen_expr(target, &mut pre);
                let v = self.gen_expr(value, &mut pre);
                if expr_always_exits(target, true) || expr_always_exits(value, true) {
                    pre
                } else {
                    format!("{}{}{} = {}\n", pre, self.ind(), t, v)
                }
            }
            Stmt::Expr(expr) => self.gen_expr_as_stmt(expr),
            Stmt::Type(td) => self.gen_type_def(td),
            Stmt::Impl(id) => self.gen_impl(id),
            Stmt::Extern { name, kind, .. } => match kind {
                ExternKind::Value(lib_path) if name == lib_path => String::new(),
                ExternKind::Value(lib_path) => {
                    format!("{}local {} = {}", self.ind(), name, lib_path)
                }
                ExternKind::Template(_) => String::new(),
            },
            Stmt::Op {
                name,
                params,
                body,
                dict_params,
                ..
            } => self.gen_function(name, params, dict_params, body),
            Stmt::Trait(_) | Stmt::TypeAlias { .. } => String::new(),
        }
    }

    fn gen_function(
        &mut self,
        name: &str,
        params: &[(Pattern, Option<Type>)],
        dict_params: &[String],
        body: &Expr,
    ) -> String {
        let lua_name = mangle_op(name);
        let ind = self.ind();
        let mut all_params: Vec<String> = dict_params.iter().cloned().collect();
        let mut pattern_destructures = String::new();
        for (i, (pat, _)) in params.iter().enumerate() {
            match pat {
                Pattern::Variable(n, _) => all_params.push(n.clone()),
                Pattern::Wildcard => all_params.push("_".to_string()),
                _ => {
                    let placeholder = format!("__p{}", i);
                    all_params.push(placeholder.clone());
                    self.indent += 2;
                    pattern_destructures
                        .push_str(&self.gen_for_pattern_bindings(pat, &placeholder));
                    self.indent -= 2;
                }
            }
        }
        let params_s = all_params.join(", ");
        let mut out = format!("{}local function {}({})\n", ind, lua_name, params_s);
        self.indent += 2;
        out.push_str(&pattern_destructures);
        out.push_str(&self.gen_expr_as_body(body));
        self.indent -= 2;
        out.push_str(&format!("{}end\n", ind));
        out
    }

    // ── Expression → inline Lua value ─────────────────────────────────────────

    fn gen_inline_call(
        &mut self,
        callee: &str,
        args: &[String],
        pre: &mut String,
    ) -> Option<String> {
        let method = self.inline_methods.get(callee)?.clone();
        if method.params.len() != args.len() {
            return None;
        }
        let subst: HashMap<String, String> = method
            .params
            .iter()
            .cloned()
            .zip(args.iter().cloned())
            .collect();
        self.gen_expr_with_subst(&method.body, &subst, pre)
    }

    fn gen_template_call(&self, callee: &str, args: &[String]) -> Option<String> {
        let template = self.extern_templates.get(callee)?;
        let mut out = String::with_capacity(template.len());
        let mut chars = template.chars().peekable();
        while let Some(ch) = chars.next() {
            if ch != '$' {
                out.push(ch);
                continue;
            }

            let mut digits = String::new();
            while let Some(next) = chars.peek() {
                if next.is_ascii_digit() {
                    digits.push(*next);
                    chars.next();
                } else {
                    break;
                }
            }

            if digits.is_empty() {
                out.push('$');
                continue;
            }

            let Ok(index) = digits.parse::<usize>() else {
                out.push('$');
                out.push_str(&digits);
                continue;
            };
            let Some(arg) = args.get(index.saturating_sub(1)) else {
                out.push('$');
                out.push_str(&digits);
                continue;
            };
            out.push_str(arg);
        }
        Some(out)
    }

    fn gen_expr_with_subst(
        &mut self,
        expr: &Expr,
        subst: &HashMap<String, String>,
        pre: &mut String,
    ) -> Option<String> {
        match &expr.kind {
            ExprKind::Ident(name) => Some(subst.get(name).cloned().unwrap_or_else(|| name.clone())),
            ExprKind::Number(n) => Some(n.to_string()),
            ExprKind::Bool(b) => Some(if *b { "1" } else { "0" }.to_string()),
            ExprKind::Unit => Some("{}".to_string()),
            ExprKind::StringLit(s) => Some(lua_string(s)),
            ExprKind::Not(e) => {
                let v = self.gen_expr_with_subst(e, subst, pre)?;
                Some(format!("({} == 0 and 1 or 0)", v))
            }
            ExprKind::Binary {
                lhs,
                op,
                rhs,
                resolved_op,
                dict_args,
                ..
            } => {
                let l = self.gen_expr_with_subst(lhs, subst, pre)?;
                let r = self.gen_expr_with_subst(rhs, subst, pre)?;
                match op {
                    BinOp::Pipe => {
                        let mut all_args = dict_args.clone();
                        all_args.push(l);
                        Some(format!("{}({})", r, all_args.join(", ")))
                    }
                    BinOp::Custom(op) => match resolved_op {
                        Some(resolved) => {
                            if dict_args.is_empty()
                                && let Some(inlined) =
                                    self.gen_inline_call(resolved, &[l.clone(), r.clone()], pre)
                            {
                                return Some(inlined);
                            }
                            if dict_args.is_empty() {
                                Some(format!("{}({}, {})", resolved, l, r))
                            } else {
                                Some(format!(
                                    "{}({}, {}, {})",
                                    resolved,
                                    dict_args.join(", "),
                                    l,
                                    r
                                ))
                            }
                        }
                        None => Some(format!("{}({}, {})", mangle_op(op), l, r)),
                    },
                }
            }
            ExprKind::Call {
                callee,
                args,
                resolved_callee,
                dict_args,
                ..
            } => {
                let callee_s = resolved_callee
                    .clone()
                    .or_else(|| self.gen_expr_with_subst(callee, subst, pre))?;
                let mut all_args: Vec<String> = dict_args.clone();
                all_args.extend(
                    args.iter()
                        .map(|arg| self.gen_expr_with_subst(arg, subst, pre))
                        .collect::<Option<Vec<_>>>()?,
                );
                if dict_args.is_empty()
                    && let Some(inlined) = self.gen_inline_call(&callee_s, &all_args, pre)
                {
                    return Some(inlined);
                }
                if dict_args.is_empty()
                    && let Some(expanded) = self.gen_template_call(&callee_s, &all_args)
                {
                    return Some(expanded);
                }
                Some(format!("{}({})", callee_s, all_args.join(", ")))
            }
            ExprKind::Tuple(items) | ExprKind::Array(items) => {
                let items_s = items
                    .iter()
                    .map(|e| self.gen_expr_with_subst(e, subst, pre))
                    .collect::<Option<Vec<_>>>()?;
                Some(format!("{{ {} }}", items_s.join(", ")))
            }
            ExprKind::Record(fields) => {
                let fields_s = fields
                    .iter()
                    .map(|(n, e)| {
                        self.gen_expr_with_subst(e, subst, pre)
                            .map(|expr| format!("{} = {}", n, expr))
                    })
                    .collect::<Option<Vec<_>>>()?;
                Some(format!("{{ {} }}", fields_s.join(", ")))
            }
            ExprKind::FieldAccess { expr, field, .. } => {
                let e = self.gen_expr_with_subst(expr, subst, pre)?;
                Some(format!("{}.{}", e, field))
            }
            ExprKind::Block { stmts, final_expr } if stmts.is_empty() => final_expr
                .as_ref()
                .map(|expr| self.gen_expr_with_subst(expr, subst, pre))
                .unwrap_or_else(|| Some("{}".to_string())),
            ExprKind::Import(_) => None,
            ExprKind::Block { .. }
            | ExprKind::If { .. }
            | ExprKind::Match { .. }
            | ExprKind::Loop(_)
            | ExprKind::Break(_)
            | ExprKind::Continue
            | ExprKind::Return(_)
            | ExprKind::Assign { .. }
            | ExprKind::Lambda { .. }
            | ExprKind::For { .. } => None,
        }
    }

    /// Returns a Lua expression string. Any required pre-statements (for loops or
    /// diverging subexpressions) are emitted into `pre`. Callers must flush `pre`
    /// before using the returned string.
    fn gen_expr(&mut self, expr: &Expr, pre: &mut String) -> String {
        match &expr.kind {
            ExprKind::Number(n) => n.to_string(),
            ExprKind::Bool(b) => if *b { "1" } else { "0" }.to_string(),
            ExprKind::Unit => "{}".to_string(),
            ExprKind::Ident(name) => name.clone(),
            ExprKind::Import(path) => match self.import_mode {
                ImportMode::Require => format!("require({}).__hern_value", lua_string(path)),
                ImportMode::Bundle => format!("{}.__hern_value", bundle_module_var(path)),
            },
            ExprKind::StringLit(s) => lua_string(s),

            ExprKind::Not(e) => {
                let v = self.gen_expr(e, pre);
                format!("({} == 0 and 1 or 0)", v)
            }
            ExprKind::Binary {
                lhs,
                op,
                rhs,
                resolved_op,
                dict_args,
                ..
            } => {
                let l = self.gen_expr(lhs, pre);
                let r = self.gen_expr(rhs, pre);
                match op {
                    BinOp::Pipe => {
                        let mut all_args = dict_args.clone();
                        all_args.push(l);
                        format!("{}({})", r, all_args.join(", "))
                    }
                    BinOp::Custom(op) => match resolved_op {
                        Some(resolved) => {
                            if dict_args.is_empty()
                                && let Some(inlined) =
                                    self.gen_inline_call(resolved, &[l.clone(), r.clone()], pre)
                            {
                                return inlined;
                            }
                            if dict_args.is_empty() {
                                format!("{}({}, {})", resolved, l, r)
                            } else {
                                format!("{}({}, {}, {})", resolved, dict_args.join(", "), l, r)
                            }
                        }
                        None => format!("{}({}, {})", mangle_op(op), l, r),
                    },
                }
            }
            ExprKind::Assign { target, value } => {
                let t = self.gen_expr(target, pre);
                let v = self.gen_expr(value, pre);
                format!("(function() {} = {}; return {{}} end)()", t, v)
            }
            ExprKind::Lambda { params, body } => {
                let mut param_names: Vec<String> = Vec::new();
                let mut pattern_destructures = String::new();
                for (i, (pat, _)) in params.iter().enumerate() {
                    match pat {
                        Pattern::Variable(n, _) => param_names.push(n.clone()),
                        Pattern::Wildcard => param_names.push("_".to_string()),
                        _ => {
                            let placeholder = format!("__p{}", i);
                            param_names.push(placeholder.clone());
                            self.indent += 2;
                            pattern_destructures
                                .push_str(&self.gen_for_pattern_bindings(pat, &placeholder));
                            self.indent -= 2;
                        }
                    }
                }
                let params_s = param_names.join(", ");
                let mut out = format!("(function({})\n", params_s);
                self.indent += 2;
                out.push_str(&pattern_destructures);
                out.push_str(&self.gen_expr_as_body(body));
                self.indent -= 2;
                out.push_str(&format!("{}end)", self.ind()));
                out
            }
            ExprKind::Call {
                callee,
                args,
                resolved_callee,
                dict_args,
                ..
            } => {
                let callee_s = resolved_callee
                    .clone()
                    .unwrap_or_else(|| self.gen_expr(callee, pre));
                let mut all_args: Vec<String> = dict_args.clone();
                all_args.extend(args.iter().map(|a| self.gen_expr(a, pre)));
                if dict_args.is_empty()
                    && let Some(inlined) = self.gen_inline_call(&callee_s, &all_args, pre)
                {
                    return inlined;
                }
                if dict_args.is_empty()
                    && let Some(expanded) = self.gen_template_call(&callee_s, &all_args)
                {
                    return expanded;
                }
                format!("{}({})", callee_s, all_args.join(", "))
            }
            ExprKind::Tuple(items) | ExprKind::Array(items) => {
                let items_s = items
                    .iter()
                    .map(|e| self.gen_expr(e, pre))
                    .collect::<Vec<_>>();
                format!("{{ {} }}", items_s.join(", "))
            }
            ExprKind::Record(fields) => {
                let fields_s = fields
                    .iter()
                    .map(|(n, e)| format!("{} = {}", n, self.gen_expr(e, pre)))
                    .collect::<Vec<_>>();
                format!("{{ {} }}", fields_s.join(", "))
            }
            ExprKind::FieldAccess { expr, field, .. } => {
                let e = self.gen_expr(expr, pre);
                format!("{}.{}", e, field)
            }

            // Loops use a temp variable (not an IIFE) so `return` inside the body
            // reaches the enclosing Lua function. `break`/`continue` use `goto` so
            // the continue label can sit at the loop bottom without conflicting with
            // Lua's "break must be the last statement in a block" restriction.
            ExprKind::Loop(body) => {
                self.loop_counter += 1;
                let loop_id = self.loop_counter;
                let tmp = self.fresh_tmp();
                let break_label = format!("_break_{}", loop_id);

                let prev_loop_id = std::mem::replace(&mut self.current_loop_id, loop_id);
                let prev_loop_tmp = std::mem::replace(&mut self.current_loop_tmp, tmp.clone());
                let prev_break =
                    std::mem::replace(&mut self.current_break_label, break_label.clone());

                let ind = self.ind();
                pre.push_str(&format!("{}local {} = nil\n", ind, tmp));
                pre.push_str(&format!("{}while true do\n", ind));
                self.indent += 2;
                pre.push_str(&self.gen_expr_as_stmt(body));
                pre.push_str(&format!("{}::_continue_{}::\n", self.ind(), loop_id));
                self.indent -= 2;
                pre.push_str(&format!("{}end\n", ind));
                pre.push_str(&format!("{}::{}::\n", ind, break_label));

                self.current_loop_id = prev_loop_id;
                self.current_loop_tmp = prev_loop_tmp;
                self.current_break_label = prev_break;
                tmp
            }

            ExprKind::For {
                pat,
                iterable,
                body,
                resolved_iter,
                ..
            } => {
                self.loop_counter += 1;
                let loop_id = self.loop_counter;
                let break_label = format!("_break_{}", loop_id);
                let tmp = self.fresh_tmp();

                let prev_loop_id = std::mem::replace(&mut self.current_loop_id, loop_id);
                let prev_loop_tmp = std::mem::replace(&mut self.current_loop_tmp, tmp.clone());
                let prev_break =
                    std::mem::replace(&mut self.current_break_label, break_label.clone());

                let iter_fn = resolved_iter.clone().unwrap_or_else(|| "nil".to_string());
                let mut iter_pre = String::new();
                let iter_s = self.gen_expr(iterable, &mut iter_pre);
                let ind = self.ind();
                pre.push_str(&iter_pre);

                let (loop_var, needs_bindings) = match pat {
                    Pattern::Variable(name, _) => (name.clone(), false),
                    Pattern::Wildcard => ("_".to_string(), false),
                    _ => (self.fresh_tmp(), true),
                };

                pre.push_str(&format!("{}local {} = {{}}\n", ind, tmp));
                pre.push_str(&format!(
                    "{}for {} in {}({}) do\n",
                    ind, loop_var, iter_fn, iter_s
                ));
                self.indent += 2;
                if needs_bindings {
                    let bindings = self.gen_for_pattern_bindings(pat, &loop_var);
                    pre.push_str(&bindings);
                }
                pre.push_str(&self.gen_expr_as_stmt(body));
                pre.push_str(&format!("{}::_continue_{}::\n", self.ind(), loop_id));
                self.indent -= 2;
                pre.push_str(&format!("{}end\n", ind));
                pre.push_str(&format!("{}::{}::\n", ind, break_label));

                self.current_loop_id = prev_loop_id;
                self.current_loop_tmp = prev_loop_tmp;
                self.current_break_label = prev_break;
                tmp
            }

            // Diverging expressions: emit the control-flow jump into `pre` and
            // return a dead placeholder — any code using the "value" is unreachable.
            ExprKind::Break(val) => {
                if let Some(e) = val {
                    let v = self.gen_expr(e, pre);
                    pre.push_str(&format!(
                        "{}{} = {}\n",
                        self.ind(),
                        self.current_loop_tmp,
                        v
                    ));
                }
                pre.push_str(&format!(
                    "{}goto {}\n",
                    self.ind(),
                    self.current_break_label
                ));
                "nil".to_string()
            }
            ExprKind::Continue => {
                pre.push_str(&format!(
                    "{}goto _continue_{}\n",
                    self.ind(),
                    self.current_loop_id
                ));
                "nil".to_string()
            }
            ExprKind::Return(val) => {
                if let Some(e) = val {
                    let v = self.gen_expr(e, pre);
                    pre.push_str(&format!("{}return {}\n", self.ind(), v));
                } else {
                    pre.push_str(&format!("{}return {{}}\n", self.ind()));
                }
                "nil".to_string()
            }

            // Structural expressions: temp-var path when a branch diverges (so the
            // goto can escape the conditional), IIFE path otherwise.
            ExprKind::If {
                cond,
                then_branch,
                else_branch,
            } => {
                if has_diverging(then_branch, true) || has_diverging(else_branch, true) {
                    let cond_s = self.gen_expr(cond, pre);
                    let tmp = self.fresh_tmp();
                    let ind = self.ind();
                    pre.push_str(&format!("{}local {} = nil\n", ind, tmp));
                    pre.push_str(&format!("{}if {} ~= 0 then\n", ind, cond_s));
                    self.indent += 2;
                    let then_s = self.gen_expr_as_assign(then_branch, &tmp);
                    pre.push_str(&then_s);
                    self.indent -= 2;
                    pre.push_str(&format!("{}else\n", ind));
                    self.indent += 2;
                    let else_s = self.gen_expr_as_assign(else_branch, &tmp);
                    pre.push_str(&else_s);
                    self.indent -= 2;
                    pre.push_str(&format!("{}end\n", ind));
                    tmp
                } else {
                    let cond_s = self.gen_expr(cond, pre);
                    let ind = self.ind();
                    let mut iife = "(function()\n".to_string();
                    self.indent += 2;
                    iife.push_str(&format!("{}if {} ~= 0 then\n", self.ind(), cond_s));
                    self.indent += 2;
                    iife.push_str(&self.gen_expr_as_body(then_branch));
                    self.indent -= 2;
                    iife.push_str(&format!("{}else\n", self.ind()));
                    self.indent += 2;
                    iife.push_str(&self.gen_expr_as_body(else_branch));
                    self.indent -= 2;
                    iife.push_str(&format!("{}end\n", self.ind()));
                    self.indent -= 2;
                    iife.push_str(&format!("{}end)()", ind));
                    iife
                }
            }
            ExprKind::Match { scrutinee, arms } => {
                if arms.iter().any(|(_, body)| has_diverging(body, true)) {
                    let scrutinee_s = self.gen_expr(scrutinee, pre);
                    let tmp = self.fresh_tmp();
                    let ind = self.ind();
                    pre.push_str(&format!("{}local {} = nil\n", ind, tmp));
                    pre.push_str(&format!("{}local _s = {}\n", ind, scrutinee_s));
                    let arms_s = self.gen_match_arms(arms, Tail::Assign(&tmp));
                    pre.push_str(&arms_s);
                    tmp
                } else {
                    let scrutinee_s = self.gen_expr(scrutinee, pre);
                    let ind = self.ind();
                    let mut iife = "(function()\n".to_string();
                    self.indent += 2;
                    iife.push_str(&format!("{}local _s = {}\n", self.ind(), scrutinee_s));
                    iife.push_str(&self.gen_match_arms(arms, Tail::Return));
                    self.indent -= 2;
                    iife.push_str(&format!("{}end)()", ind));
                    iife
                }
            }
            ExprKind::Block { stmts, final_expr } => {
                let diverging = stmts.iter().any(|s| has_diverging_stmt(s, true))
                    || final_expr.as_ref().is_some_and(|e| has_diverging(e, true));
                if diverging {
                    let tmp = self.fresh_tmp();
                    let ind = self.ind();
                    pre.push_str(&format!("{}local {} = nil\n", ind, tmp));
                    pre.push_str(&format!("{}do\n", ind));
                    self.indent += 2;
                    let mut reachable = true;
                    for stmt in stmts {
                        if !reachable {
                            break;
                        }
                        pre.push_str(&self.gen_stmt(stmt));
                        pre.push('\n');
                        reachable = !stmt_always_exits(stmt, true);
                    }
                    if reachable && let Some(e) = final_expr {
                        let assign_s = self.gen_expr_as_assign(e, &tmp);
                        pre.push_str(&assign_s);
                    }
                    self.indent -= 2;
                    pre.push_str(&format!("{}end\n", ind));
                    tmp
                } else {
                    let ind = self.ind();
                    let mut iife = "(function()\n".to_string();
                    self.indent += 2;
                    for stmt in stmts {
                        iife.push_str(&self.gen_stmt(stmt));
                        iife.push('\n');
                    }
                    if let Some(e) = final_expr {
                        iife.push_str(&self.gen_expr_as_body(e));
                    }
                    self.indent -= 2;
                    iife.push_str(&format!("{}end)()", ind));
                    iife
                }
            }
        }
    }

    // ── Tail-position generation ──────────────────────────────────────────────

    /// Generates code for `expr` in a position where the value is consumed by
    /// `tail`. Structural expressions (`if`/`match`/`block`) are flattened
    /// directly rather than wrapped in IIFEs, enabling Lua TCO for recursive calls.
    fn gen_tail(&mut self, expr: &Expr, tail: Tail<'_>) -> String {
        let ind = self.ind();
        match &expr.kind {
            ExprKind::Block { stmts, final_expr } => {
                let mut out = String::new();
                let mut reachable = true;
                for stmt in stmts {
                    if !reachable {
                        break;
                    }
                    out.push_str(&self.gen_stmt(stmt));
                    out.push('\n');
                    reachable = !stmt_always_exits(stmt, true);
                }
                if reachable && let Some(e) = final_expr {
                    out.push_str(&self.gen_tail(e, tail));
                }
                out
            }
            ExprKind::If {
                cond,
                then_branch,
                else_branch,
            } => {
                let mut pre = String::new();
                let cond_s = self.gen_expr(cond, &mut pre);
                let mut out = pre;
                out.push_str(&format!("{}if {} ~= 0 then\n", ind, cond_s));
                self.indent += 2;
                out.push_str(&self.gen_tail(then_branch, tail));
                self.indent -= 2;
                out.push_str(&format!("{}else\n", ind));
                self.indent += 2;
                out.push_str(&self.gen_tail(else_branch, tail));
                self.indent -= 2;
                out.push_str(&format!("{}end\n", ind));
                out
            }
            ExprKind::Match { scrutinee, arms } => {
                let mut pre = String::new();
                let scrutinee_s = self.gen_expr(scrutinee, &mut pre);
                let mut out = pre;
                out.push_str(&format!("{}local _s = {}\n", ind, scrutinee_s));
                out.push_str(&self.gen_match_arms(arms, tail));
                out
            }
            ExprKind::Break(val) => {
                let mut out = String::new();
                if let Some(e) = val {
                    let mut pre = String::new();
                    let v = self.gen_expr(e, &mut pre);
                    out.push_str(&pre);
                    out.push_str(&format!("{}{} = {}\n", ind, self.current_loop_tmp, v));
                }
                out.push_str(&format!("{}goto {}\n", ind, self.current_break_label));
                out
            }
            ExprKind::Continue => {
                format!("{}goto _continue_{}\n", ind, self.current_loop_id)
            }
            ExprKind::Return(val) => {
                let mut out = String::new();
                if let Some(e) = val {
                    let mut pre = String::new();
                    let v = self.gen_expr(e, &mut pre);
                    out.push_str(&pre);
                    out.push_str(&format!("{}return {}\n", ind, v));
                } else {
                    out.push_str(&format!("{}return {{}}\n", ind));
                }
                out
            }
            // For loops produce Unit; just emit as a statement.
            ExprKind::For { .. } => {
                let mut pre = String::new();
                let _ = self.gen_expr(expr, &mut pre);
                pre
            }
            _ => {
                let mut pre = String::new();
                let val = self.gen_expr(expr, &mut pre);
                if expr_always_exits(expr, true) {
                    return pre;
                }
                match tail {
                    Tail::Return => format!("{}{}return {}\n", pre, ind, val),
                    Tail::Discard => format!("{}{}local _ = {}\n", pre, ind, val),
                    Tail::Assign(name) => format!("{}{}{} = {}\n", pre, ind, name, val),
                }
            }
        }
    }

    fn gen_expr_as_body(&mut self, expr: &Expr) -> String {
        self.gen_tail(expr, Tail::Return)
    }

    fn gen_expr_as_stmt(&mut self, expr: &Expr) -> String {
        self.gen_tail(expr, Tail::Discard)
    }

    fn gen_expr_as_assign(&mut self, expr: &Expr, target: &str) -> String {
        self.gen_tail(expr, Tail::Assign(target))
    }

    fn gen_for_pattern_bindings(&mut self, pat: &Pattern, var: &str) -> String {
        match pat {
            Pattern::Wildcard | Pattern::StringLit(_) | Pattern::Variable(_, _) => String::new(),
            Pattern::Constructor { binding, .. } => match binding {
                Some((v, _)) => format!("{}local {} = {}._0\n", self.ind(), v, var),
                None => String::new(),
            },
            Pattern::Record { fields, rest } => {
                let mut out = String::new();
                for (field, binding, _) in fields {
                    out.push_str(&format!(
                        "{}local {} = {}.{}\n",
                        self.ind(),
                        binding,
                        var,
                        field
                    ));
                }
                if let Some(Some((rest_name, _))) = rest {
                    let ind = self.ind();
                    out.push_str(&format!("{}local {} = {{}}\n", ind, rest_name));
                    out.push_str(&format!("{}for _k, _v in pairs({}) do\n", ind, var));
                    self.indent += 2;
                    let guards = fields
                        .iter()
                        .map(|(f, _, _)| format!("_k ~= \"{}\"", f))
                        .collect::<Vec<_>>();
                    if guards.is_empty() {
                        out.push_str(&format!("{}{}[_k] = _v\n", self.ind(), rest_name));
                    } else {
                        out.push_str(&format!("{}if {} then\n", self.ind(), guards.join(" and ")));
                        self.indent += 2;
                        out.push_str(&format!("{}{}[_k] = _v\n", self.ind(), rest_name));
                        self.indent -= 2;
                        out.push_str(&format!("{}end\n", self.ind()));
                    }
                    self.indent -= 2;
                    out.push_str(&format!("{}end\n", self.ind()));
                }
                out
            }
            Pattern::List { elements, rest } => {
                let mut out = String::new();
                for (i, elem) in elements.iter().enumerate() {
                    match elem {
                        Pattern::Variable(name, _) if name != "_" => {
                            out.push_str(&format!(
                                "{}local {} = {}[{}]\n",
                                self.ind(),
                                name,
                                var,
                                i + 1
                            ));
                        }
                        Pattern::Wildcard => {}
                        _ => {
                            let tmp = self.fresh_tmp();
                            out.push_str(&format!(
                                "{}local {} = {}[{}]\n",
                                self.ind(),
                                tmp,
                                var,
                                i + 1
                            ));
                            out.push_str(&self.gen_for_pattern_bindings(elem, &tmp));
                        }
                    }
                }
                if let Some(Some((rest_name, _))) = rest {
                    let start = elements.len() + 1;
                    out.push_str(&format!(
                        "{}local {} = {{_unpack({}, {})}}\n",
                        self.ind(),
                        rest_name,
                        var,
                        start
                    ));
                }
                out
            }
            Pattern::Tuple(elems) => {
                let mut out = String::new();
                for (i, elem) in elems.iter().enumerate() {
                    match elem {
                        Pattern::Variable(name, _) if name != "_" => {
                            out.push_str(&format!(
                                "{}local {} = {}[{}]\n",
                                self.ind(),
                                name,
                                var,
                                i + 1
                            ));
                        }
                        Pattern::Wildcard => {}
                        _ => {
                            // Nested destructuring: emit a fresh temp and recurse.
                            let tmp = self.fresh_tmp();
                            out.push_str(&format!(
                                "{}local {} = {}[{}]\n",
                                self.ind(),
                                tmp,
                                var,
                                i + 1
                            ));
                            out.push_str(&self.gen_for_pattern_bindings(elem, &tmp));
                        }
                    }
                }
                out
            }
        }
    }

    // ── Pattern matching ──────────────────────────────────────────────────────

    fn gen_match_arms(&mut self, arms: &[(Pattern, Expr)], tail: Tail<'_>) -> String {
        let mut out = String::new();
        let mut first = true;
        let mut closed = false;

        for (pat, body) in arms {
            match self.gen_pattern_cond(pat) {
                Some(cond) => {
                    let kw = if first { "if" } else { "elseif" };
                    first = false;
                    out.push_str(&format!("{}{} {} then\n", self.ind(), kw, cond));
                    self.indent += 2;
                    out.push_str(&self.gen_pattern_bindings(pat));
                    out.push_str(&self.gen_tail(body, tail));
                    self.indent -= 2;
                }
                None => {
                    if !first {
                        out.push_str(&format!("{}else\n", self.ind()));
                        self.indent += 2;
                    }
                    out.push_str(&self.gen_pattern_bindings(pat));
                    out.push_str(&self.gen_tail(body, tail));
                    if !first {
                        self.indent -= 2;
                        out.push_str(&format!("{}end\n", self.ind()));
                        closed = true;
                    }
                    break;
                }
            }
        }

        if !first && !closed {
            out.push_str(&format!("{}end\n", self.ind()));
        }
        out
    }

    fn gen_pattern_cond(&self, pat: &Pattern) -> Option<String> {
        self.gen_pattern_cond_for(pat, "_s")
    }

    /// Generate the runtime guard condition for `pat` where the scrutinee is `var`.
    /// Returns `None` if the pattern is always-irrefutable at runtime.
    fn gen_pattern_cond_for(&self, pat: &Pattern, var: &str) -> Option<String> {
        match pat {
            Pattern::Wildcard | Pattern::Variable(_, _) | Pattern::Record { .. } => None,
            Pattern::StringLit(s) => Some(format!("{} == {}", var, lua_string(s))),
            Pattern::Constructor { name, .. } => Some(format!("{}._tag == \"{}\"", var, name)),
            Pattern::List { elements, rest } => {
                let n = elements.len();
                let len_cond = match (n, rest.is_none()) {
                    (0, true) => Some(format!("#{} == 0", var)),
                    (n, true) => Some(format!("#{} == {}", var, n)),
                    (0, false) => None,
                    (n, false) => Some(format!("#{} >= {}", var, n)),
                };
                let elem_conds = elements.iter().enumerate().filter_map(|(i, elem)| {
                    let sub_var = format!("{}[{}]", var, i + 1);
                    self.gen_pattern_cond_for(elem, &sub_var)
                });
                let conds: Vec<String> = len_cond.into_iter().chain(elem_conds).collect();
                if conds.is_empty() {
                    None
                } else {
                    Some(conds.join(" and "))
                }
            }
            Pattern::Tuple(elems) => {
                // Collect per-element conditions, checking each at `var[i+1]`.
                let conds: Vec<String> = elems
                    .iter()
                    .enumerate()
                    .filter_map(|(i, elem)| {
                        let sub_var = format!("{}[{}]", var, i + 1);
                        self.gen_pattern_cond_for(elem, &sub_var)
                    })
                    .collect();
                if conds.is_empty() {
                    None
                } else {
                    Some(conds.join(" and "))
                }
            }
        }
    }

    fn gen_pattern_bindings(&mut self, pat: &Pattern) -> String {
        match pat {
            Pattern::Wildcard | Pattern::StringLit(_) | Pattern::Variable(_, _) => String::new(),
            Pattern::Constructor { binding, .. } => match binding {
                Some((v, _)) => format!("{}local {} = _s._0\n", self.ind(), v),
                None => String::new(),
            },
            Pattern::Record { fields, rest } => {
                let mut out = String::new();
                for (field, binding, _) in fields {
                    out.push_str(&format!("{}local {} = _s.{}\n", self.ind(), binding, field));
                }
                if let Some(Some((rest_name, _))) = rest {
                    let ind = self.ind();
                    out.push_str(&format!("{}local {} = {{}}\n", ind, rest_name));
                    out.push_str(&format!("{}for _k, _v in pairs(_s) do\n", ind));
                    self.indent += 2;
                    let guards = fields
                        .iter()
                        .map(|(f, _, _)| format!("_k ~= \"{}\"", f))
                        .collect::<Vec<_>>();
                    if guards.is_empty() {
                        out.push_str(&format!("{}{}[_k] = _v\n", self.ind(), rest_name));
                    } else {
                        out.push_str(&format!("{}if {} then\n", self.ind(), guards.join(" and ")));
                        self.indent += 2;
                        out.push_str(&format!("{}{}[_k] = _v\n", self.ind(), rest_name));
                        self.indent -= 2;
                        out.push_str(&format!("{}end\n", self.ind()));
                    }
                    self.indent -= 2;
                    out.push_str(&format!("{}end\n", self.ind()));
                }
                out
            }
            Pattern::List { elements, rest } => {
                let mut out = String::new();
                for (i, elem) in elements.iter().enumerate() {
                    match elem {
                        Pattern::Variable(name, _) if name != "_" => {
                            out.push_str(&format!(
                                "{}local {} = _s[{}]\n",
                                self.ind(),
                                name,
                                i + 1
                            ));
                        }
                        Pattern::Wildcard => {}
                        _ => {
                            let tmp = self.fresh_tmp();
                            out.push_str(&format!("{}local {} = _s[{}]\n", self.ind(), tmp, i + 1));
                            out.push_str(&self.gen_for_pattern_bindings(elem, &tmp));
                        }
                    }
                }
                if let Some(Some((rest_name, _))) = rest {
                    let start = elements.len() + 1;
                    out.push_str(&format!(
                        "{}local {} = {{_unpack(_s, {})}}\n",
                        self.ind(),
                        rest_name,
                        start
                    ));
                }
                out
            }
            Pattern::Tuple(_) => {
                // Tuples are Lua integer-indexed arrays; bind by position.
                self.gen_for_pattern_bindings(pat, "_s")
            }
        }
    }

    // ── Type definitions / trait impls ────────────────────────────────────────

    fn gen_type_def(&self, td: &TypeDef) -> String {
        let ind = self.ind();
        td.variants
            .iter()
            .map(|v| {
                if v.payload.is_some() {
                    format!(
                        "{}local function {}(_0) return {{ _tag = \"{}\", _0 = _0 }} end\n",
                        ind, v.name, v.name
                    )
                } else {
                    format!("{}local {} = {{ _tag = \"{}\" }}\n", ind, v.name, v.name)
                }
            })
            .collect()
    }

    fn gen_impl(&mut self, id: &ImplDef) -> String {
        let dict_name = format!("__{}__{}", id.trait_name, impl_target_name(&id.target));
        let ind = self.ind();
        let mut out = format!("{}local {} = {{\n", ind, dict_name);
        self.indent += 2;
        for method in &id.methods {
            let mut param_names: Vec<String> = Vec::new();
            let mut pattern_destructures = String::new();
            for (i, (pat, _)) in method.params.iter().enumerate() {
                match pat {
                    Pattern::Variable(n, _) => param_names.push(n.clone()),
                    Pattern::Wildcard => param_names.push("_".to_string()),
                    _ => {
                        let placeholder = format!("__p{}", i);
                        param_names.push(placeholder.clone());
                        self.indent += 2;
                        pattern_destructures
                            .push_str(&self.gen_for_pattern_bindings(pat, &placeholder));
                        self.indent -= 2;
                    }
                }
            }
            let params = param_names.join(", ");
            out.push_str(&format!(
                "{}{} = function({})\n",
                self.ind(),
                mangle_op(&method.name),
                params
            ));
            self.indent += 2;
            out.push_str(&pattern_destructures);
            out.push_str(&self.gen_expr_as_body(&method.body));
            self.indent -= 2;
            out.push_str(&format!("{}end,\n", self.ind()));
        }
        self.indent -= 2;
        out.push_str(&format!("{}}}", self.ind()));
        out
    }
}

// ── Control-flow analysis ─────────────────────────────────────────────────────

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Flow {
    FallsThrough,
    MayExit,
    AlwaysExits,
}

impl Flow {
    fn contains_exit(self) -> bool {
        self != Flow::FallsThrough
    }

    fn always_exits(self) -> bool {
        self == Flow::AlwaysExits
    }

    fn seq(self, next: Flow) -> Flow {
        match (self, next) {
            (Flow::AlwaysExits, _) | (_, Flow::AlwaysExits) => Flow::AlwaysExits,
            (Flow::MayExit, _) | (_, Flow::MayExit) => Flow::MayExit,
            (Flow::FallsThrough, Flow::FallsThrough) => Flow::FallsThrough,
        }
    }

    fn branch(lhs: Flow, rhs: Flow) -> Flow {
        match (lhs, rhs) {
            (Flow::AlwaysExits, Flow::AlwaysExits) => Flow::AlwaysExits,
            (Flow::FallsThrough, Flow::FallsThrough) => Flow::FallsThrough,
            _ => Flow::MayExit,
        }
    }
}

/// `include_bc = false` crosses a loop boundary: `break`/`continue` are captured
/// by that loop, but `return` still exits the enclosing function.
fn expr_flow(expr: &Expr, include_bc: bool) -> Flow {
    match &expr.kind {
        ExprKind::Return(_) => Flow::AlwaysExits,
        ExprKind::Break(_) | ExprKind::Continue => {
            if include_bc {
                Flow::AlwaysExits
            } else {
                Flow::FallsThrough
            }
        }
        ExprKind::Loop(body) => expr_flow(body, false),
        ExprKind::For { iterable, body, .. } => {
            expr_flow(iterable, include_bc).seq(match expr_flow(body, false) {
                Flow::FallsThrough => Flow::FallsThrough,
                _ => Flow::MayExit,
            })
        }
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
        } => expr_flow(cond, include_bc).seq(Flow::branch(
            expr_flow(then_branch, include_bc),
            expr_flow(else_branch, include_bc),
        )),
        ExprKind::Block { stmts, final_expr } => {
            let mut flow = Flow::FallsThrough;
            for stmt in stmts {
                flow = flow.seq(stmt_flow(stmt, include_bc));
                if flow.always_exits() {
                    return flow;
                }
            }
            if let Some(expr) = final_expr {
                flow.seq(expr_flow(expr, include_bc))
            } else {
                flow
            }
        }
        ExprKind::Match { scrutinee, arms } => {
            let arm_flow = if arms.is_empty() {
                Flow::FallsThrough
            } else {
                arms.iter()
                    .map(|(_, body)| expr_flow(body, include_bc))
                    .reduce(Flow::branch)
                    .unwrap_or(Flow::FallsThrough)
            };
            expr_flow(scrutinee, include_bc).seq(arm_flow)
        }
        ExprKind::Not(e) | ExprKind::FieldAccess { expr: e, .. } => expr_flow(e, include_bc),
        ExprKind::Binary { lhs, rhs, .. } => {
            expr_flow(lhs, include_bc).seq(expr_flow(rhs, include_bc))
        }
        ExprKind::Assign { target, value } => {
            expr_flow(target, include_bc).seq(expr_flow(value, include_bc))
        }
        ExprKind::Call { callee, args, .. } => args
            .iter()
            .fold(expr_flow(callee, include_bc), |flow, arg| {
                flow.seq(expr_flow(arg, include_bc))
            }),
        ExprKind::Tuple(es) | ExprKind::Array(es) => {
            es.iter().fold(Flow::FallsThrough, |flow, expr| {
                flow.seq(expr_flow(expr, include_bc))
            })
        }
        ExprKind::Record(fields) => fields.iter().fold(Flow::FallsThrough, |flow, (_, expr)| {
            flow.seq(expr_flow(expr, include_bc))
        }),
        ExprKind::Lambda { .. }
        | ExprKind::Number(_)
        | ExprKind::StringLit(_)
        | ExprKind::Bool(_)
        | ExprKind::Ident(_)
        | ExprKind::Import(_)
        | ExprKind::Unit => Flow::FallsThrough,
    }
}

fn stmt_flow(stmt: &Stmt, include_bc: bool) -> Flow {
    match stmt {
        Stmt::Expr(expr) | Stmt::Let { value: expr, .. } => expr_flow(expr, include_bc),
        _ => Flow::FallsThrough,
    }
}

fn has_diverging(expr: &Expr, include_bc: bool) -> bool {
    expr_flow(expr, include_bc).contains_exit()
}

fn has_diverging_stmt(stmt: &Stmt, include_bc: bool) -> bool {
    stmt_flow(stmt, include_bc).contains_exit()
}

fn expr_always_exits(expr: &Expr, include_bc: bool) -> bool {
    expr_flow(expr, include_bc).always_exits()
}

fn stmt_always_exits(stmt: &Stmt, include_bc: bool) -> bool {
    stmt_flow(stmt, include_bc).always_exits()
}

// ── Helpers ───────────────────────────────────────────────────────────────────

pub(crate) fn mangle_op(name: &str) -> String {
    if name.chars().all(|c| c.is_alphanumeric() || c == '_') {
        return name.to_string();
    }
    let mut s = String::from("__op_");
    for c in name.chars() {
        match c {
            '<' => s.push_str("lt"),
            '>' => s.push_str("gt"),
            '~' => s.push_str("tl"),
            '@' => s.push_str("at"),
            '?' => s.push_str("qm"),
            '$' => s.push_str("dl"),
            '^' => s.push_str("ht"),
            '*' => s.push_str("st"),
            '/' => s.push_str("sl"),
            '%' => s.push_str("pc"),
            '+' => s.push_str("pl"),
            '-' => s.push_str("mn"),
            '=' => s.push_str("eq"),
            '!' => s.push_str("bn"),
            '&' => s.push_str("am"),
            '|' => s.push_str("pp"),
            '.' => s.push_str("dt"),
            _ => s.push(c),
        }
    }
    s
}

fn impl_target_name(target: &Type) -> String {
    match target {
        Type::Ident(name) => name.clone(),
        Type::App(con, _) => impl_target_name(con),
        _ => "Unknown".to_string(),
    }
}

fn split_module_body(stmts: &[Stmt]) -> (&[Stmt], Option<&Expr>) {
    match stmts.last() {
        Some(Stmt::Expr(expr)) => (&stmts[..stmts.len() - 1], Some(expr)),
        _ => (stmts, None),
    }
}

fn impl_dict_names(program: &Program) -> Vec<String> {
    impl_dict_names_from_stmts(&program.stmts)
}

fn impl_dict_names_from_stmts(stmts: &[Stmt]) -> Vec<String> {
    stmts
        .iter()
        .filter_map(|stmt| {
            if let Stmt::Impl(id) = stmt {
                Some(format!(
                    "__{}__{}",
                    id.trait_name,
                    impl_target_name(&id.target)
                ))
            } else {
                None
            }
        })
        .collect()
}

fn collect_pattern_names(pat: &Pattern, names: &mut Vec<String>) {
    match pat {
        Pattern::Variable(name, _) => names.push(name.clone()),
        Pattern::Wildcard | Pattern::StringLit(_) | Pattern::Constructor { binding: None, .. } => {}
        Pattern::Constructor {
            binding: Some((name, _)),
            ..
        } => names.push(name.clone()),
        Pattern::Record { fields, rest } => {
            for (_, binding, _) in fields {
                names.push(binding.clone());
            }
            if let Some(Some((rest_name, _))) = rest {
                names.push(rest_name.clone());
            }
        }
        Pattern::List { elements, rest } => {
            for elem in elements {
                collect_pattern_names(elem, names);
            }
            if let Some(Some((rest_name, _))) = rest {
                names.push(rest_name.clone());
            }
        }
        Pattern::Tuple(elems) => {
            for elem in elems {
                collect_pattern_names(elem, names);
            }
        }
    }
}

fn prelude_value_names(stmts: &[Stmt]) -> Vec<String> {
    let mut names = Vec::new();
    for stmt in stmts {
        match stmt {
            Stmt::Extern {
                name,
                kind: ExternKind::Value(_),
                ..
            } => names.push(name.clone()),
            Stmt::Fn { name, .. } | Stmt::Op { name, .. } => names.push(mangle_op(name)),
            Stmt::Type(td) => {
                names.extend(td.variants.iter().map(|variant| variant.name.clone()));
            }
            Stmt::Let { pat, .. } => collect_pattern_names(pat, &mut names),
            Stmt::Extern {
                kind: ExternKind::Template(_),
                ..
            }
            | Stmt::Expr(_)
            | Stmt::Trait(_)
            | Stmt::Impl(_)
            | Stmt::TypeAlias { .. } => {}
        }
    }
    names.sort();
    names.dedup();
    names
}

fn bundle_module_var(name: &str) -> String {
    format!("__mod_{}", name)
}

fn lua_string(s: &str) -> String {
    let escaped = s
        .replace('\\', "\\\\")
        .replace('"', "\\\"")
        .replace('\n', "\\n")
        .replace('\r', "\\r")
        .replace('\t', "\\t");
    format!("\"{}\"", escaped)
}
