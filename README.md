# Hern

Hern is an experimental statically typed language that compiles to Lua.

It is a small language for exploring expressive type inference, structural
data, traits that can talk about more than one type at once, and practical
scripting ergonomics without carrying a large runtime. Source files use the
`.hern` extension, and extensionless imports resolve to `.hern` files.

The name started as **Highly Expressive Rusty Notation**. The current shape is
closer to: ML-style inference, Rust-flavored traits and impls, structural
records that can remain open over the fields a function does not touch,
algebraic data types, explicit mutation, and Lua as the portable execution
target.

Hern is not a production language. It is a working compiler, standard library,
CLI, REPL, and language server for testing language-design ideas in real code.
The compiler parses and typechecks Hern, resolves traits by passing explicit
dictionaries, then emits Lua that can be printed, bundled, or executed.

## Current Status

Hern is best understood as a language workbench:

- The core compiler, CLI, REPL, LSP, and integration test suite are active and
  usable.
- The standard library is deliberately compact, with enough primitives to write
  examples, algorithms, parser combinators, and small numeric programs.
- The language favors clear static semantics over production hardening. Expect
  sharp edges, evolving syntax, and occasional migration work as the type system
  improves.

## A Taste

```hern
fn map_pair(f, (x, y)) {
  (f(x), f(y))
}

let inc = fn(x) { x + 1 };
let answer = Some(map_pair(inc, (1, 2)));

match answer {
  Some((left, right)) -> print(left + right),
  None -> print(0),
}
```

Hern infers ordinary local types, lambda parameters, many function signatures,
records, tuples, arrays, and generic functions. Record types are structural, so
a function can ask for the fields it uses while preserving the rest of the
caller-provided value. Add annotations where they make an API clearer:

```hern
fn length_squared(x: float, y: float) -> float {
  x * x + y * y
}
```

Mutation is explicit, but it is not just a boolean on a variable. Hern tracks
fresh mutable places so mutating methods can be called on newly allocated values
without opening the door to casual aliasing:

```hern
let mut values = [];
values.push(1);
values.push(2);
```

## What It Supports

- Hindley-Milner-style type inference with parametric polymorphism.
- Algebraic data types such as `Option('a)` and `Result('a, 'e)`.
- Pattern matching for constructors, tuples, records, arrays, literals, and
  wildcards.
- Row-polymorphic records, so functions can require only the fields they use.
- Traits, impl blocks, associated functions, and operator methods.
- Multi-parameter traits with functional dependencies, used by operators like
  `Add`, `Mul`, and `Index`.
- Higher-kinded trait parameters for abstractions like `Functor`.
- Explicit `let mut` mutation with place tracking for mutable method calls.
- Modules through file imports and record-shaped exports.
- Lua code generation, including single-file bundles.
- LSP support for diagnostics, hover, definitions, references, document
  highlights, document/workspace symbols, rename, completions, signature help,
  code actions, semantic tokens, and inlay hints.

## Traits And Operators

Simple trait constraints look like this:

```hern
fn show_twice(value: 'a) -> string
where 'a: ToString
{
  value.to_string() <> value.to_string()
}
```

Traits are compiled away through dictionaries, but at the source level they can
still describe fairly rich relationships. Multi-parameter traits put all
parameters before the trait name. Functional dependencies use `->` before the
determined output type:

```hern
trait Mul 'lhs 'rhs -> 'output {
  fn infixl 7 *(lhs: 'lhs, rhs: 'rhs) -> 'output
}

fn scale(value: 'value, factor: float) -> 'out
where 'value float -> 'out: Mul
{
  value * factor
}
```

That shape lets `*` mean `int * int -> int`, `float * float -> float`, and also
library-defined operations such as `Matrix * Vector -> Vector`.

Trait parameters can also be type constructors, which is how the prelude defines
abstractions such as `Functor`, `Applicative`, and `Monad` for `Option`,
`Result`, arrays, and parser combinators.

## Standard Library

The standard library is intentionally small, but it is real enough to write
programs. The prelude is also where many language ideas are exercised: operators
are ordinary traits, indexing is a functional-dependency trait, and common data
types such as `Option`, `Result`, `Map`, `Heap`, `Queue`, and `Set` are available
without extra imports.

- `std/prelude.hern`: core types, traits, operators, collections, ranges, JSON
  helpers, and Lua-backed primitives.
- `std/grid.hern`: a compact generic grid helper.
- `std/parser.hern`: parser-combinator utilities.
- `std/linalg.hern`: small linear algebra types for vectors and matrices.
- `std/astar.hern`: generic A* path search over caller-defined node types.

Example import:

```hern
let linalg = import "hern:linalg";

let v = linalg.vector([3.0, 4.0]);
print(v.length());
```

Modules export values with record syntax, and imports bind that record:

The final expression of a module is its export value. When that final
expression is a record, fields that directly re-export a named binding keep
that binding's generalized type scheme:

```hern
fn id(x) { x }

#{ id: id }
```

Inline expressions are inferred as ordinary record field values instead:

```hern
#{ id: fn(x) { x } }
```

So prefer naming reusable generic exports before placing them in the final
record.

```hern
let astar = import "hern:astar";

fn key(n: int) -> string { n.to_string() }
fn neighbors(n: int) -> [int] { if n == 0 { [1] } else { [] } }

let path = astar.search(
  0,
  fn(n) { n == 1 },
  key,
  neighbors,
  fn(a, b) { 1.0 },
  fn(n) { 0.0 }
);
```

## CLI

Build the CLI:

```sh
cargo build -p hern
```

Run a file:

```sh
cargo run -p hern -- path/to/file.hern
```

Available commands:

```sh
cargo run -p hern -- parse path/to/file.hern
cargo run -p hern -- typecheck path/to/file.hern
cargo run -p hern -- typecheck --dump path/to/file.hern
cargo run -p hern -- lua path/to/file.hern
cargo run -p hern -- run path/to/file.hern
cargo run -p hern -- test path/to/file.hern
cargo run -p hern -- bundle path/to/file.hern
cargo run -p hern -- repl
cargo run -p hern -- repl path/to/file.hern
cargo run -p hern -- lsp
```

`lua` prints generated Lua. `bundle` emits a self-contained Lua bundle. `run`
typechecks, compiles, and executes through the local Lua runtime used by the
REPL.

Unit tests live in `test` blocks. Functions marked with `#[test]` are run by
`hern test`; unmarked functions in the block can be used as test helpers.
Normal `run`, `lua`, and `bundle` output omits test blocks.

```hern
test {
  fn expected() {
    Some(2)
  }

  #[test]
  fn option_map_some() {
    assert_eq(Some(1).map(fn(x) { x + 1 }), expected())
  }
}
```

The prelude provides `assert_eq` and `assert_ne` for tests and other checks.
Both require `Eq + ToString` so failures can include the compared values.

Hern can derive structural `Eq` and `ToString` implementations for sum types:

```hern
#[derive(Eq, ToString)]
type Box('a) = Box('a)

print(Box(1) == Box(1))   // true
print(to_string(Box(2)))  // Box(2)
```

## Workspace

- `hern-core`: lexer, parser, type inference, modules, source indexing, and Lua
  code generation.
- `hern`: CLI.
- `hern-repl`: interactive REPL.
- `hern-lsp`: language server.
- `std`: standard library modules loaded through `hern:` imports.
- `tests/hern`: integration fixtures used by `tests/run.py`.
- `examples`: sample Hern programs and experiments.

## Development

Useful checks:

```sh
cargo fmt
cargo check --workspace
cargo test -p hern-core
cargo test -p hern-lsp
cargo test -p hern
python3 tests/run.py
```

The integration runner compiles and executes the fixture programs under
`tests/hern`, including expected-error cases.

## Examples

The `examples` directory contains larger experiments and demos. The `tests/hern`
fixtures are also useful as executable language documentation because each one
is typechecked, run, or expected to fail with a specific diagnostic.
