# Hern

Hern is **Highly Expressive Rusty Notation**: a small statically typed language
with Hindley-Milner-style inference, structural data, traits, modules, and Lua
code generation.

Source files use the `.hern` extension. Extensionless imports resolve to `.hern` files.

## Language

Hern is expression-oriented and infers types for ordinary code without requiring
annotations at every binding. Function signatures may be explicit when useful,
but local values, lambdas, array literals, records, and many function
declarations can be inferred.

```hern
fn map_pair(f, pair) {
  let (x, y) = pair;
  (f(x), f(y))
}

let inc = fn(x) { x + 1 };
map_pair(inc, (1, 2))
```

The type system has:

- Parametric polymorphism: functions can quantify over unconstrained type
  variables like `'a` and `'b`.
- Trait constraints: generic functions can require capabilities without fixing a
  concrete type.
- Row-polymorphic records: functions can ask for fields they use while
  preserving the rest of the record.
- Algebraic data types: sum types with constructors and payloads.
- Pattern matching: tuples, records, arrays/lists, constructors, literals,
  wildcards, and destructuring in `let`, function parameters, `match`, and
  `for`.
- Typed mutation: `let mut` is explicit, and assignment checks the existing
  binding type.
- Modules: files can import other `.hern` modules and export values through
  record-shaped module results.

```hern
fn get_x(r) {
  r.x
}

let point = #{ x: 1, y: 2, label: "origin" };
get_x(point)
```

That style gives `get_x` a record-polymorphic shape: it only cares that `x` exists, not what other fields are present.

Traits are resolved through dictionaries during lowering, then emitted as Lua. The generated Lua is intended to be readable enough for debugging while keeping Hern's type information in the compiler.

The language server currently supports diagnostics, hover type hints, go-to-definition, references, rename, and completion from scope.

## Build

```sh
cargo build -p hern
```

## CLI

```sh
cargo run -p hern -- parse path/to/file.hern
cargo run -p hern -- typecheck path/to/file.hern
cargo run -p hern -- lua path/to/file.hern
cargo run -p hern -- run path/to/file.hern
cargo run -p hern -- bundle path/to/file.hern
cargo run -p hern -- lsp
```

The `lua` command prints generated Lua. The `run` command executes generated Lua through a local Lua runtime.

## Workspace

- `hern-core`: lexer, parser, type inference, module loading, source indexing, and Lua code generation.
- `hern`: CLI.
- `hern-lsp`: language server support for diagnostics, hover, definitions, references, rename, and completions.
- `std/prelude.hern`: built-in prelude loaded by the compiler.
- `tests/hern`: integration fixtures.

## Test

```sh
cargo test -q -p hern-core
cargo test -q -p hern-lsp
cargo test -q -p hern
python3 tests/run.py
```
