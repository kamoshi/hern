//! Macro definition inference.
//!
//! Macro bodies are phase-1 Hern: they are checked at authoring time, produce
//! normal editor metadata, and must return `MacroResult(Syntax)`. The current
//! macro executor still supports a restricted expression subset, but typing
//! lives here so the compiler and LSP have one explicit phase-1 entry point.

use super::state::TypeScope;
use super::*;

impl Infer {
    pub(super) fn infer_macro_defs(
        &mut self,
        env: &TypeEnv,
        defs: &mut [MacroDef],
    ) -> Result<(), SpannedTypeError> {
        for def in defs {
            self.infer_macro_def(env, def)?;
        }
        Ok(())
    }

    fn infer_macro_def(
        &mut self,
        env: &TypeEnv,
        def: &mut MacroDef,
    ) -> Result<(), SpannedTypeError> {
        let syntax_ty = Ty::Con("Syntax".to_string());
        let mut param_vars = HashMap::new();
        let param_ty = self
            .ast_to_ty_with_vars(&def.param_ty, &mut param_vars)
            .map_err(|err| err.at(def.param_ty_span))?;
        if param_ty != syntax_ty {
            return Err(TypeError::InvalidMacroSignature {
                message: format!("input parameter must have type `Syntax`, got `{param_ty}`"),
            }
            .at(def.param_ty_span));
        }

        let ret_ty = self
            .ast_to_ty_with_vars(&def.ret_ty, &mut param_vars)
            .map_err(|err| err.at(def.ret_ty_span))?;
        let expected_ret_ty = macro_result_syntax_ty();
        if ret_ty != expected_ret_ty {
            return Err(TypeError::InvalidMacroSignature {
                message: format!("return type must be `MacroResult(Syntax)`, got `{ret_ty}`"),
            }
            .at(def.ret_ty_span));
        }

        if !matches!(def.body.kind, ExprKind::Block { .. }) {
            return Err(TypeError::InvalidMacroSignature {
                message: "body must be a block expression".to_string(),
            }
            .at(def.body.span));
        }

        let mut macro_env = macro_phase_env(env);
        self.metadata
            .record_binding_type(def.param_span, syntax_ty.clone());
        macro_env.insert(
            def.param_name.clone(),
            EnvInfo::immutable(Scheme::mono(syntax_ty.clone())),
        );

        let body_ty = self.infer_expr(&macro_env, &mut def.body)?;
        unify(&mut self.subst, body_ty, macro_result_syntax_ty())
            .map_err(|err| err.at(def.body.span))
    }
}

fn macro_result_syntax_ty() -> Ty {
    Ty::App(
        Box::new(Ty::Con("Result".to_string())),
        vec![
            Ty::Con("Syntax".to_string()),
            Ty::Con("MacroError".to_string()),
        ],
    )
}

pub(super) fn register_macro_phase_type_surface(types: &mut TypeScope) {
    for (name, arity) in [
        ("Syntax", 0),
        ("SyntaxMeta", 0),
        ("SyntaxDelimiter", 0),
        ("SyntaxToken", 0),
        ("Hygiene", 0),
        ("MacroError", 0),
        ("Result", 2),
        ("MacroResult", 1),
        ("Option", 1),
    ] {
        types.declared.insert(name.to_string());
        types.constructor_arities.insert(name.to_string(), arity);
    }
    types.aliases.insert(
        "MacroResult".to_string(),
        (
            vec!["a".to_string()],
            Type::App(
                Box::new(Type::Ident("Result".to_string())),
                vec![
                    Type::Var("a".to_string()),
                    Type::Ident("MacroError".to_string()),
                ],
            ),
        ),
    );
}

fn macro_phase_env(env: &TypeEnv) -> TypeEnv {
    let mut phase_env = TypeEnv::new();
    for (name, info) in env.iter() {
        if info.macro_phase_available || macro_builtin_available(name) {
            phase_env.insert(name.clone(), info.clone());
        }
    }
    insert_syntax_builtin_schemes(&mut phase_env);
    phase_env
}

pub(super) fn insert_syntax_builtin_schemes(env: &mut TypeEnv) {
    let syntax = Ty::Con("Syntax".to_string());
    let bool_ty = Ty::Con("bool".to_string());
    let string_ty = Ty::Con("string".to_string());
    let array_string = array_ty(string_ty.clone());
    let delimiter = Ty::Con("SyntaxDelimiter".to_string());
    let macro_error = Ty::Con("MacroError".to_string());
    let macro_result_syntax = macro_result_syntax_ty();
    let syntax_to_syntax = Ty::Func(
        value_func_params(vec![syntax.clone()]),
        value_func_return(syntax.clone()),
    );
    let syntax_to_bool = Ty::Func(
        value_func_params(vec![syntax.clone()]),
        value_func_return(bool_ty.clone()),
    );
    let option_delimiter = Ty::App(
        Box::new(Ty::Con("Option".to_string())),
        vec![delimiter.clone()],
    );
    let option_string = Ty::App(
        Box::new(Ty::Con("Option".to_string())),
        vec![string_ty.clone()],
    );
    let span_tuple = Ty::Tuple(vec![Ty::Int, Ty::Int, Ty::Int, Ty::Int]);
    let builtins = [
        (
            "syntax_children",
            Ty::Func(
                value_func_params(vec![syntax.clone()]),
                value_func_return(array_ty(syntax.clone())),
            ),
        ),
        (
            "syntax_delimiter",
            Ty::Func(
                value_func_params(vec![syntax.clone()]),
                value_func_return(option_delimiter),
            ),
        ),
        (
            "syntax_kind",
            Ty::Func(
                value_func_params(vec![syntax.clone()]),
                value_func_return(string_ty.clone()),
            ),
        ),
        (
            "syntax_span",
            Ty::Func(
                value_func_params(vec![syntax.clone()]),
                value_func_return(span_tuple),
            ),
        ),
        (
            "syntax_origin",
            Ty::Func(
                value_func_params(vec![syntax.clone()]),
                value_func_return(string_ty.clone()),
            ),
        ),
        (
            "syntax_token_text",
            Ty::Func(
                value_func_params(vec![syntax.clone()]),
                value_func_return(option_string.clone()),
            ),
        ),
        (
            "syntax_is_ident",
            Ty::Func(
                value_func_params(vec![syntax.clone(), string_ty.clone()]),
                value_func_return(bool_ty.clone()),
            ),
        ),
        (
            "syntax_eq_shape",
            Ty::Func(
                value_func_params(vec![syntax.clone(), syntax.clone()]),
                value_func_return(bool_ty.clone()),
            ),
        ),
        (
            "syntax_same_binding",
            Ty::Func(
                value_func_params(vec![syntax.clone(), syntax.clone()]),
                value_func_return(bool_ty),
            ),
        ),
        (
            "syntax_token",
            Ty::Func(
                value_func_params(vec![Ty::Con("SyntaxToken".to_string())]),
                value_func_return(Ty::Con("Syntax".to_string())),
            ),
        ),
        (
            "syntax_tree",
            Ty::Func(
                value_func_params(vec![delimiter, array_ty(Ty::Con("Syntax".to_string()))]),
                value_func_return(Ty::Con("Syntax".to_string())),
            ),
        ),
        (
            "syntax_sequence",
            Ty::Func(
                value_func_params(vec![array_ty(Ty::Con("Syntax".to_string()))]),
                value_func_return(Ty::Con("Syntax".to_string())),
            ),
        ),
        (
            "syntax_ident",
            Ty::Func(
                value_func_params(vec![string_ty.clone()]),
                value_func_return(Ty::Con("Syntax".to_string())),
            ),
        ),
        (
            "syntax_literal",
            Ty::Func(
                value_func_params(vec![string_ty.clone()]),
                value_func_return(Ty::Con("Syntax".to_string())),
            ),
        ),
        (
            "syntax_operator",
            Ty::Func(
                value_func_params(vec![string_ty.clone()]),
                value_func_return(Ty::Con("Syntax".to_string())),
            ),
        ),
        (
            "syntax_punct",
            Ty::Func(
                value_func_params(vec![string_ty]),
                value_func_return(Ty::Con("Syntax".to_string())),
            ),
        ),
        (
            "syntax_fresh_ident",
            Ty::Func(
                value_func_params(vec![Ty::Con("string".to_string())]),
                value_func_return(Ty::Con("Syntax".to_string())),
            ),
        ),
        (
            "syntax_ident_at_use_site",
            Ty::Func(
                value_func_params(vec![Ty::Con("string".to_string())]),
                value_func_return(Ty::Con("Syntax".to_string())),
            ),
        ),
        (
            "syntax_map_children",
            Ty::Func(
                value_func_params(vec![syntax.clone(), syntax_to_syntax]),
                value_func_return(syntax.clone()),
            ),
        ),
        (
            "syntax_find",
            Ty::Func(
                value_func_params(vec![syntax.clone(), syntax_to_bool]),
                value_func_return(Ty::App(
                    Box::new(Ty::Con("Option".to_string())),
                    vec![syntax.clone()],
                )),
            ),
        ),
        (
            "syntax_replace",
            Ty::Func(
                value_func_params(vec![syntax.clone(), syntax.clone(), syntax.clone()]),
                value_func_return(syntax.clone()),
            ),
        ),
        (
            "syntax_join",
            Ty::Func(
                value_func_params(vec![array_ty(syntax.clone()), syntax.clone()]),
                value_func_return(syntax.clone()),
            ),
        ),
        (
            "syntax_debug",
            Ty::Func(
                value_func_params(vec![syntax]),
                value_func_return(Ty::Con("string".to_string())),
            ),
        ),
        (
            "macro_resolve_ident",
            Ty::Func(
                value_func_params(vec![Ty::Con("Syntax".to_string())]),
                value_func_return(option_string.clone()),
            ),
        ),
        (
            "macro_type_of",
            Ty::Func(
                value_func_params(vec![Ty::Con("Syntax".to_string())]),
                value_func_return(option_string),
            ),
        ),
        (
            "macro_fields_of",
            Ty::Func(
                value_func_params(vec![Ty::Con("Syntax".to_string())]),
                value_func_return(array_string.clone()),
            ),
        ),
        (
            "macro_variants_of",
            Ty::Func(
                value_func_params(vec![Ty::Con("Syntax".to_string())]),
                value_func_return(array_string.clone()),
            ),
        ),
        (
            "macro_trait_methods_of",
            Ty::Func(
                value_func_params(vec![Ty::Con("Syntax".to_string())]),
                value_func_return(array_string.clone()),
            ),
        ),
        (
            "macro_module_items",
            Ty::Func(
                value_func_params(vec![Ty::Con("Syntax".to_string())]),
                value_func_return(array_string),
            ),
        ),
        (
            "Ok",
            Ty::Func(
                value_func_params(vec![Ty::Con("Syntax".to_string())]),
                value_func_return(macro_result_syntax.clone()),
            ),
        ),
        (
            "Err",
            Ty::Func(
                value_func_params(vec![macro_error.clone()]),
                value_func_return(macro_result_syntax),
            ),
        ),
        (
            "MacroError",
            Ty::Func(
                value_func_params(vec![Ty::Con("string".to_string())]),
                value_func_return(macro_error),
            ),
        ),
    ];
    for (name, ty) in builtins {
        if env.get(name).is_none() {
            env.insert(name.to_string(), EnvInfo::immutable(Scheme::mono(ty)));
        }
    }
}

fn macro_builtin_available(name: &str) -> bool {
    matches!(
        name,
        "Ok" | "Err"
            | "MacroError"
            | "syntax_children"
            | "syntax_delimiter"
            | "syntax_kind"
            | "syntax_span"
            | "syntax_origin"
            | "syntax_token_text"
            | "syntax_is_ident"
            | "syntax_eq_shape"
            | "syntax_same_binding"
            | "syntax_token"
            | "syntax_tree"
            | "syntax_sequence"
            | "syntax_ident"
            | "syntax_literal"
            | "syntax_operator"
            | "syntax_punct"
            | "syntax_fresh_ident"
            | "syntax_ident_at_use_site"
            | "syntax_map_children"
            | "syntax_find"
            | "syntax_replace"
            | "syntax_join"
            | "syntax_debug"
            | "macro_resolve_ident"
            | "macro_type_of"
            | "macro_fields_of"
            | "macro_variants_of"
            | "macro_trait_methods_of"
            | "macro_module_items"
            | "Paren"
            | "Brace"
            | "Bracket"
            | "Keyword"
            | "Literal"
            | "Operator"
            | "Punct"
            | "to_string"
    )
}
