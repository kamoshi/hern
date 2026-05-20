# Hern Macros

Status: current implementation guide.

Hern has first-class syntax values, quasiquotes, quote patterns, and same-file
expression macros. The macro system is intentionally small today: macro authors
transform `Syntax` into `MacroResult(Syntax)`, and the compiler parses the
returned syntax back as ordinary Hern.

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

This is deliberately not Hern's internal typed AST. It is stable user-facing
syntax data that can be matched, rebuilt, printed for debugging, and later
expanded by macros.

`ToString for Syntax` produces normalized debug-ish source. It joins syntax
children with spaces, so it is deterministic but not a promise to round-trip
original formatting.

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

- `expr`
- `type`
- `pat`
- `block`
- `ident`
- `literal`
- `operator`
- `punct`
- `token`
- `tree`
- `tokens`

`expr`, `type`, and `pat` are checked with parser-backed fragment parsers.
Token-level categories are checked against the token-tree shape.

## Expression Macros

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

The current implementation supports same-file expression macros only. Macro
definitions are collected before ordinary code is typechecked, macro bodies are
typechecked, and macro calls are expanded before Lua codegen.

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

Currently supported macro-phase expressions include:

- literals: `int`, `float`, `bool`, `string`, `()`
- identifiers and lexical scope
- `let`
- blocks
- `if`
- `match`
- same-file helper function calls
- whitelisted pure helpers such as `syntax_children`, `syntax_token_text`,
  `syntax_is_ident`, and `to_string`
- arrays, tuples, records
- field access and indexing
- `==`, `!=`, `&&`, `||`
- integer `+`, `-`, `<`, `<=`, `>`, `>=`
- local assignment
- `loop` and `break`, bounded by the macro step limit
- syntax quotes and template splices

Unsupported macro-phase constructs are rejected with compiler diagnostics rather
than being passed through to runtime codegen.

## Current Limitations

- Macros are same-file only.
- Macro imports are not implemented.
- Item, attribute, derive, pattern, and type macros are not implemented.
- Hygiene has a foundation, but macro-introduced scopes are not yet the final
  hygienic model.
- Source-map/origin diagnostics for expanded code are still basic.
- The macro prelude is minimal and currently lives alongside the ordinary
  prelude helpers.
- Parse-back uses normalized syntax source, so precedence-sensitive expansion
  needs more hardening before the feature is production-grade.

The accepted execution-model direction is documented in
`docs/macro-execution-model.md`.
