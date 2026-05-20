# Hern Macros

Status: current implementation guide.

Hern has first-class syntax values, quasiquotes, quote patterns, expression
macros, and top-level item macros. The macro system is intentionally small:
macro authors transform `Syntax` into `MacroResult(Syntax)`, and the compiler
parses the returned syntax back as ordinary Hern.

## Macros In 5 Minutes

Use a macro when a normal function cannot express the source shape you need.
Macros receive unevaluated syntax and return replacement syntax.

```hern
macro unless(input: Syntax) -> MacroResult(Syntax) {
  match input {
    '{$cond:expr, $body:block} -> Ok('{ if $cond { () } else { $body } }),
    _ -> Err(MacroError("unless expects a condition and block")),
  }
}

let mut n = 0;
unless!(n == 3, {
  n = n + 1;
});
```

The `$cond:expr` and `$body:block` names are syntax-pattern captures. The
returned quote splices those captures with `$cond` and `$body`. If the input
does not match, return `Err(MacroError(...))`; the compiler reports it at the
macro call site with macro-definition context.

## Syntax Values

Quoted syntax is written with an apostrophe immediately followed by a delimiter:

```hern
let call = '{foo(1, x + y)};
let group = '(x + y);
let list = '[a, b, c];
```

The public syntax model is a token tree:

```hern
type Syntax =
  Token((SyntaxToken, SyntaxMeta))
  | Tree((SyntaxDelimiter, [Syntax], SyntaxMeta))
  | Sequence(([Syntax], SyntaxMeta))
```

`SyntaxMeta` is intentionally opaque in Hern code:

```hern
type SyntaxMeta = *
```

Use `syntax_span` and `syntax_origin` to inspect metadata; the origin string is
currently `"source"` or `"generated"`.

This is deliberately not Hern's internal typed AST. It is stable user-facing
syntax data that can be matched, rebuilt, printed for debugging, and later
expanded by macros.

`ToString for Syntax` produces normalized debug-ish source. It joins syntax
children with spaces, so it is deterministic but not a promise to round-trip
original formatting. Compiler parse-back uses a separate Rust-side normalized
printer with source-map tracking; user code should treat `to_string(syntax)` and
`syntax_debug(syntax)` as inspection tools, not as the macro expansion ABI.

Small constructor helpers are available when quasiquotes are too rigid:

```hern
let expr = syntax_sequence([
  syntax_literal("1"),
  syntax_operator("+"),
  syntax_literal("2"),
]);
let call = syntax_tree(Paren, [syntax_ident("f"), syntax_tree(Paren, [])]);
```

Constructed syntax uses generated metadata. `syntax_token` accepts an existing
`SyntaxToken`; the focused helpers `syntax_ident`, `syntax_literal`,
`syntax_operator`, and `syntax_punct` are usually more convenient.
`syntax_fresh_ident(base)` creates an identifier with a fresh generated scope;
two fresh identifiers with the same text are not the same binding.
`syntax_ident_at_use_site(base)` creates an identifier in the macro call site's
scope for deliberate capture; prefer fresh or template-introduced identifiers
unless capture is intentional.

Pure syntax helper operations are also available in runtime code and macro
bodies:

- `syntax_map_children(s, f)` rebuilds only the direct children of a tree or
  sequence.
- `syntax_find(s, pred)` searches syntax in pre-order and returns
  `Option(Syntax)`.
- `syntax_replace(s, target, replacement)` recursively replaces nodes with the
  same syntax shape as `target`.
- `syntax_join(nodes, sep)` returns a sequence with `sep` inserted between
  nodes.
- `syntax_debug(s)` returns deterministic structural text for diagnostics and
  tests.

## Quote Patterns

Syntax quotes can appear in `match` patterns:

```hern
match syntax {
  '{$lhs:expr + $rhs:expr} -> '{ $rhs + $lhs },
  _ -> syntax,
}
```

Pattern captures use `$name:category`. Repeat captures use `...`:

```hern
match syntax {
  '{$items:token...} -> items,
  _ -> [],
}
```

Templates splice captured values with `$name` or `$name...`:

```hern
match '{answer + 41} {
  '{$lhs:expr + $rhs:expr} -> '{ $lhs * $rhs },
  _ -> '{0},
}
```

Supported categories are:

- `expr`: a complete Hern expression fragment.
- `type`: a complete Hern type fragment.
- `pat`: a complete Hern pattern fragment.
- `block`: a brace-delimited block expression.
- `ident`: an identifier token.
- `literal`: a number, string, `true`, or `false` token.
- `operator`: an operator token such as `+`, `==`, or a custom operator.
- `punct`: punctuation such as `.`, `,`, `:`, or `;`.
- `token`: one non-delimiter token of any category.
- `tokens`: zero or more syntax nodes in repeat captures.
- `tree`: one delimited syntax tree.

`expr`, `type`, and `pat` are checked with parser-backed fragment parsers.
Token-level categories are checked against the token-tree shape.

Examples that intentionally fail:

```hern
match '{foo(} {
  '{$x:expr} -> x,
  _ -> '{0},
}
```

The `expr` capture does not match because `foo(` is not a complete expression.

```hern
match '{x + y} {
  '{$x + $y} -> '{0},
  _ -> '{1},
}
```

Pattern captures require categories; write `$x:expr` or another category.

## Expression And Item Macros

A macro definition is a top-level phase-1 declaration:

```hern
macro unless(input: Syntax) -> MacroResult(Syntax) {
  match input {
    '{$cond:expr, $body:block} -> Ok('{ if $cond { () } else { $body } }),
    _ -> Err(MacroError("unless expects a condition and block")),
  }
}
```

A macro call uses `!`:

```hern
unless!(done, {
  step();
});
```

Macro definitions are collected before ordinary code is typechecked, macro
bodies are typechecked, and macro calls are expanded before Lua codegen.

If a top-level macro call expands to an expression, it remains a top-level
expression statement. If it expands to item/declaration syntax, the compiler
parses the generated syntax as top-level statements:

```hern
macro make_answer(input: Syntax) -> MacroResult(Syntax) {
  Ok(syntax_sequence(syntax_children('{
    fn answer() { 42 }
  })))
}

make_answer!(());

print(to_string(answer()));
```

Item macros use the same runtime, source-map, hygiene metadata, expansion fuel,
and diagnostics as expression macros.

For a module, the compile-time order is:

1. Parse the module.
2. Resolve ordinary imports enough to load macro-providing dependencies.
3. Expand expression macros using local macros plus macros from imported modules.
4. Resolve imports again so imports generated by macros are ordinary module
   imports.
5. Expand derives.
6. Reassociate operators.
7. Typecheck and codegen.

Ordinary module imports also bring that module's top-level macros into macro
scope:

```hern
let macros = import "my_macros";

my_macro!(1, 2);
```

Macro names live in a namespace separate from values and types. Imported macro
names are unqualified today; if two imports provide the same macro name, or an
imported macro conflicts with a local macro, the compiler rejects the module
instead of guessing. An imported macro runs with helper functions from its
defining module, not with same-named helpers from the caller.

## Macro-Phase Runtime

Macro bodies run in an isolated compiler-owned comptime runtime. The runtime is
bounded and deterministic. It has:

- expansion fuel
- macro evaluation step limits
- macro helper call depth limits
- output syntax node limits
- generated source byte limits before parse-back

Macro code cannot access files, network, processes, environment variables,
wall-clock time, randomness, runtime externs, or compiler internals.

The macro prelude is compiler-owned. Even in a `#![no_implicit_prelude]`
module, macro signatures may use `Syntax`, `MacroError`, and
`MacroResult(Syntax)`, and macro bodies may call the whitelisted syntax helpers
such as `syntax_kind`. Ordinary runtime prelude values are still not available
in macro phase; for example, `print` is not a macro-phase builtin.

Currently supported macro-phase expressions include:

- literals: `int`, `float`, `bool`, `string`, `()`
- identifiers and lexical scope
- `let`
- blocks
- `if`
- `match`
- helper function calls from the macro's defining module
- whitelisted pure helpers such as `syntax_children`, `syntax_delimiter`,
  `syntax_kind`, `syntax_span`, `syntax_origin`, `syntax_token_text`,
  `syntax_is_ident`, `syntax_eq_shape`, `syntax_same_binding`,
  `syntax_token`, `syntax_tree`, `syntax_sequence`, `syntax_ident`,
  `syntax_literal`, `syntax_operator`, `syntax_punct`, `syntax_fresh_ident`,
  `syntax_ident_at_use_site`, `syntax_map_children`, `syntax_find`,
  `syntax_replace`, `syntax_join`, `syntax_debug`, and `to_string`
- arrays, tuples, records
- field access and indexing
- `==`, `!=`, `&&`, `||`
- integer `+`, `-`, `<`, `<=`, `>`, `>=`
- local assignment
- `loop` and `break`, bounded by the macro step limit
- syntax quotes and template splices

Unsupported macro-phase constructs are rejected with compiler diagnostics rather
than being passed through to runtime codegen.

## Hygiene In Hern

Syntax identifiers carry scope metadata. Template-introduced identifiers receive
macro-introduction scope, `syntax_fresh_ident` creates a fresh generated scope,
and `syntax_ident_at_use_site` deliberately creates an identifier in the call
site scope.

Use this rule of thumb:

- Write identifiers directly in a template when the macro owns them.
- Use `syntax_fresh_ident` when creating temporary bindings that must not
  collide with caller names.
- Use `syntax_ident_at_use_site` only when deliberate capture is the feature.
- Use `syntax_same_binding` to compare identifiers with scope sensitivity.

## Debugging Macro Expansion

Use `hern expand` to inspect generated syntax without adding debug prints:

```sh
hern expand path/to/file.hern --all
hern expand path/to/file.hern --macro unless
hern expand path/to/file.hern --at 12:5 --with-origins
hern expand path/to/file.hern --json
```

The output includes the original macro call, normalized generated source, and
origin annotations when requested. Parse-back and type errors from expanded code
include related information for the macro call and macro definition.

Inside macro code, `syntax_debug(syntax)` and `to_string(syntax)` are useful for
deterministic test output. They are not formatting-preserving printers.

## Macro Limitations And Phase Rules

Macro execution is phase-1 only. It cannot observe runtime values, call runtime
externs, import modules inside a macro body, mutate global runtime state, read
files, use IO, inspect the clock, or use randomness.

The compiler rejects unsupported macro-phase constructs. For example:

```hern
macro bad(input: Syntax) -> MacroResult(Syntax) {
  print("debug");
  Ok(input)
}
```

This fails because `print` is a runtime prelude function, not a macro-phase
helper.

```hern
macro bad(input: Syntax) -> MacroResult(Syntax) {
  let dep = import "tools";
  Ok(input)
}
```

This fails because macro execution cannot perform imports from inside the macro
body.

## Current Limitations

- Imported macros are unqualified; explicit macro import lists and qualified
  macro calls are not implemented.
- Attribute, derive, pattern, and type macros are not implemented.
- Item macros are currently top-level `name!(...)` calls that expand to
  declarations/items. Attribute-style item targets are future work.
- Hygiene tracks source, macro-introduction, use-site, and fresh generated
  scopes on syntax values. `syntax_same_binding` and identifier shape equality
  include those scopes.
- The macro prelude is minimal and compiler-owned; phase-1 execution sees only
  whitelisted pure helpers.
- Reflection APIs such as `macro_type_of` and `macro_fields_of` are not
  implemented.

The accepted execution-model direction is documented in
`docs/macro-execution-model.md`.
