# First-Class Derive Plan

This plan adds first-class deriving for Hern traits, starting with `Eq` and
`ToString`.

Target user-facing syntax:

```hern
#[derive(Eq, ToString)]
type Option('a) = Some('a) | None
```

Target lowering:

```hern
impl Eq for Option('a)
where 'a: Eq
{
  fn ==(lhs, rhs) { ... }
  fn !=(lhs, rhs) { !(lhs == rhs) }
}

impl ToString for Option('a)
where 'a: ToString
{
  fn to_string(self) { ... }
}
```

The guiding design is: derive should synthesize ordinary Hern AST that then
flows through the existing reassociation, type inference, dictionary resolution,
LSP metadata, and Lua codegen paths. Derive should be a compiler pass, not a
parallel typeclass implementation mechanism.

## Prior Art

- Haskell `deriving (Eq, Show)` is the closest semantic model: a clause on a
  data declaration generates ordinary typeclass instances, and generic
  constraints are inferred from fields.
- Rust `#[derive(PartialEq, Eq, Debug)]` is the closest surface syntax: an
  attribute on a type declaration expands to generated `impl` items and uses an
  internal marker such as `automatically_derived` for tools.
- OCaml `[@@deriving show, eq]` is the best implementation lesson: separate the
  common type-shape traversal from each specific deriver, keep generated code
  hygienic, and make plugin-specific errors name the deriver that failed.

For Hern, the main takeaway is to build one shared derive lowering layer that
extracts the type shape once, then lets `Eq` and `ToString` generate different
method bodies from that shape.

## Current Codebase Shape

Relevant existing pieces:

- `hern-core/src/ast/mod.rs`
  - `Stmt::Type(TypeDef)` stores nominal sum types.
  - `Stmt::Impl(ImplDef)` stores trait impls.
  - `TypeDef` has `name`, `params`, and `variants`.
  - `Variant` has `name` and optional single `payload`.
  - `Attribute` already exists for `#[test]` functions.
- `hern-core/src/parse/mod.rs`
  - `parse_outer_attrs` currently accepts only `#[test]` before functions.
  - `parse_type_def_stmt` parses both sum types and aliases.
  - `parse_impl_stmt` already creates the exact `ImplDef` nodes derive should
    synthesize.
- `hern-core/src/pipeline.rs`, `hern-core/src/module.rs`,
  `hern-core/src/analysis.rs`
  - Programs are parsed, imports are resolved, then reassociated, then inferred.
  - Module loading has both fail-fast and recovering paths.
  - Prelude analysis also uses parse -> reassociate -> infer.
- `hern-core/src/types/infer.rs`
  - The inference pre-pass builds constructor envs from `Stmt::Type`.
  - Trait impls are normal top-level statements.
  - Collecting inference removes current-program impl names until impl
    statements succeed, so generated impls should be ordinary statements.
- `hern-core/src/codegen/lua.rs`
  - Type definitions emit constructors.
  - Trait impls emit dictionaries.
  - If derive lowers to `Stmt::Impl`, codegen needs no special derive support.
- `std/prelude.hern`
  - `Option` and `Result` already have handwritten `ToString` impls.
  - `Eq` and `ToString` trait shapes are good initial targets.

Important current limitation:

- Generic `impl Eq for Option('a) where 'a: Eq` did not previously satisfy
  `Eq for Option(int)` reliably during the test feature work. Derive should
  either fix this first or include it as the first milestone, because deriving
  concrete impls only would be the wrong architecture.

## Proposed Architecture

Add a new module:

```rust
// hern-core/src/derive.rs
pub fn expand_derives(program: &mut Program) -> Result<Vec<CompilerDiagnostic>, CompilerDiagnostic>;
pub fn expand_derives_recovering(program: &mut Program) -> Vec<CompilerDiagnostic>;
```

The exact API can be adjusted, but it should support:

- fail-fast parsing/loading paths;
- recovering LSP/workspace paths;
- diagnostics that point to the derive attribute span;
- mutation of `program.stmts` by inserting generated `Stmt::Impl` items.

Keep the pass before reassociation:

```text
parse
resolve imports
expand derives
reassociate
infer
codegen
```

Reasons:

- Generated method bodies will contain operators such as `==`, `!=`, `<>`, and
  `&&`, so they need the existing reassociation pass.
- Generated impls should participate in normal type inference and dictionary
  resolution.
- LSP should see the final generated behavior through the same compiler metadata
  paths, while source diagnostics still point back to the derive attribute.

## AST Changes

Extend type definitions:

```rust
pub struct DeriveAttr {
    pub traits: Vec<DeriveTrait>,
    pub span: SourceSpan,
}

pub enum DeriveTrait {
    Eq,
    ToString,
}

pub struct TypeDef {
    pub span: SourceSpan,
    pub name: String,
    pub name_span: SourceSpan,
    pub params: Vec<String>,
    pub variants: Vec<Variant>,
    pub derives: Vec<DeriveAttr>,
}
```

Keep `Attribute` for general syntax if useful, but typed derive data should be
stored on `TypeDef`; this avoids repeatedly validating strings later.

Also add an optional generated marker to impls:

```rust
pub enum GeneratedBy {
    Derive {
        trait_name: String,
        source_span: SourceSpan,
    },
}

pub struct ImplDef {
    ...
    pub generated_by: Option<GeneratedBy>,
}
```

This is not required for codegen, but it is useful for diagnostics, LSP, future
linting, and distinguishing handwritten impls in tests.

If that field causes too much churn initially, keep an internal side table in
the derive pass and add the marker in a follow-up. The higher-quality endpoint
is to mark generated impls explicitly.

## Parser Plan

Support only:

```hern
#[derive(Eq)]
#[derive(Eq, ToString)]
type Name('a) = ...
```

Rules:

- `#[derive(...)]` is allowed only on `type` declarations.
- `#[test]` remains allowed only on functions inside `test { ... }`.
- Unknown derive traits produce a parse diagnostic, e.g.
  `Cannot derive Unknown: supported derives are Eq, ToString`.
- Attributes before aliases should initially error:
  `derive is only supported for sum type declarations`.
  This keeps v1 focused and avoids unclear alias semantics.
- Empty derive list is an error.
- Multiple derive attributes compose in source order.
- Duplicate derive names on one type are an error.

Implementation details:

- Generalize `parse_outer_attrs` enough to parse `#[derive(Eq, ToString)]`
  without confusing `#{ ... }` record literals.
- In `parse_stmt_in_context`, if attributes appear before `type`, pass them to
  `parse_type_def_stmt_with_attrs`.
- Validate context in the parser so LSP gets fast, local errors.
- Store the derive span so later lowering/type errors can point at the source
  attribute.

## Shared Derive Model

Create a common intermediate shape:

```rust
struct DeriveInput<'a> {
    source_span: SourceSpan,
    type_name: &'a str,
    type_params: &'a [String],
    variants: Vec<DeriveVariant<'a>>,
}

struct DeriveVariant<'a> {
    name: &'a str,
    name_span: SourceSpan,
    payload: Option<&'a Type>,
}
```

Shared helpers:

- `impl_target(input) -> Type`
  - `Option('a)` for parametric types.
  - `Ordering` for nullary monomorphic types.
- `type_param_bounds(input, trait_name) -> Vec<TypeBound>`
  - v1: add one bound per type parameter that appears anywhere in a variant
    payload.
  - Example: `Option('a)` deriving `Eq` gets `where 'a: Eq`.
  - Example: `Result('a, 'e)` deriving `ToString` gets
    `where 'a: ToString, 'e: ToString`.
- `variant_pattern(name, binding_names) -> Pattern`
- `synthetic_expr(kind) -> Expr`
- `synthetic_param(name) -> Param`
- `qualified_trait_call(trait_name, method, args) -> Expr`
  - Generates `ToString::to_string(value)` style AST.
- `binary(lhs, op, rhs) -> Expr`
  - Generates unresolved custom-op AST; reassociation and inference resolve it.

Do not generate source strings and reparse them. Generate AST directly.

## Derive Eq

Generated shape for nullary variants:

```hern
impl Eq for Ordering {
  fn ==(lhs, rhs) {
    match lhs {
      LT -> match rhs { LT -> true, _ -> false },
      EQ -> match rhs { EQ -> true, _ -> false },
      GT -> match rhs { GT -> true, _ -> false },
    }
  }

  fn !=(lhs, rhs) {
    !(lhs == rhs)
  }
}
```

Generated shape for payload variants:

```hern
impl Eq for Option('a)
where 'a: Eq
{
  fn ==(lhs, rhs) {
    match lhs {
      Some(l0) -> match rhs {
        Some(r0) -> l0 == r0,
        _ -> false,
      },
      None -> match rhs {
        None -> true,
        _ -> false,
      },
    }
  }

  fn !=(lhs, rhs) {
    !(lhs == rhs)
  }
}
```

Notes:

- Hern variants currently have at most one payload type. Tuple payloads already
  exist as a single `Type::Tuple`, so field-wise comparison can simply compare
  the payload value and rely on existing tuple `Eq`.
- The generated `!=` should use `!(lhs == rhs)` to avoid duplicating the full
  comparison tree.
- The wildcard arm should use `Pattern::Wildcard` for all non-matching
  constructors.
- If the type has zero variants, reject v1 deriving with a clear diagnostic.

## Derive ToString

Generated shape:

```hern
impl ToString for Option('a)
where 'a: ToString
{
  fn to_string(self) {
    match self {
      Some(value) -> "Some(" <> ToString::to_string(value) <> ")",
      None -> "None",
    }
  }
}
```

For tuple payloads, v1 can rely on `ToString` for the tuple payload as a single
value if tuple `ToString` exists. If not, the derived impl will fail during
normal type inference with a missing `ToString` diagnostic.

String formatting policy:

- Nullary variant: `"Name"`.
- Payload variant: `"Name(" <> ToString::to_string(payload) <> ")"`.
- Do not include module paths in v1.
- Do not add customization attributes in v1.
- Do not special-case strings; use the existing `ToString for string`.

This intentionally follows Haskell/OCaml structural display more than Rust
`Display`. Hern users opt in explicitly, so a structural `ToString` is acceptable.

## Generic Impl Resolution Prerequisite

Before enabling std to use derived generic `Eq`, add focused tests around this
case:

```hern
type Box('a) = Box('a)

impl Eq for Box('a)
where 'a: Eq
{
  fn ==(lhs, rhs) {
    match lhs {
      Box(l) -> match rhs {
        Box(r) -> l == r,
      },
    }
  }

  fn !=(lhs, rhs) { !(lhs == rhs) }
}

print(to_string(Box(1) == Box(1)))
```

Expected behavior:

- `Box(int)` resolves to the generic `Eq for Box('a)` impl.
- Missing payload bounds still produce a clean missing-impl diagnostic.

If this fails, fix applied generic impl resolution first. Derive depends on this
for every parametric type.

## Pipeline Integration

Fail-fast paths:

- `analysis::analyze_prelude_source`
- `analysis::analyze_source`
- `module::load_module`
- `module::parse_imported_module`
  if applicable

Recovering paths:

- `module::load_module_recovering`
- any LSP parse/source analysis path that uses `parse_source_recovering`

Concrete steps:

1. Add `derive` module to `hern-core/src/lib.rs`.
2. Call `expand_derives_fail_fast(&mut program)` after import resolution and
   before reassociation in module loading.
3. Call it after parsing and before reassociation for prelude/single-source
   analysis.
4. In recovering paths, collect derive diagnostics and keep the original type
   declaration while skipping only the failed generated impls.
5. Ensure generated impls are inserted immediately after the source `type`
   declaration. This keeps source order deterministic and makes conflict
   diagnostics easier to understand.

## LSP And Source Indexing

Because generated impls have synthetic spans, avoid exposing them as ordinary
document symbols or rename targets in v1.

Expectations:

- Hover/completion on the source type should still work.
- Diagnostics from malformed derive syntax point at `#[derive(...)]`.
- Type errors inside a generated impl should be remapped to the derive
  attribute span when possible.
- References/rename should not offer generated method definitions as editable
  source ranges.

Practical v1 rule:

- generated AST nodes use `SourceSpan::synthetic()`;
- generated impl has `generated_by` containing the real derive span;
- when inference reports an error on a synthetic span within a generated impl,
  convert it to the derive span before surfacing diagnostics.

If remapping all nested synthetic diagnostics is too large for v1, at least make
the derive pass generate explicit preflight errors for unsupported shapes so
most user mistakes are caught before inference.

## Conflict Rules

Use existing impl conflict machinery as much as possible.

Policy:

- Deriving a trait and manually implementing the same trait for the exact same
  target in the same module should be an error.
- The diagnostic should mention both the derive attribute and the existing impl
  if possible.
- Two derive attributes that request the same trait for the same type should be
  a parse/lowering error before inference.
- Imported impl conflicts should remain governed by existing module env rules.

Implementation:

- v1 can rely on existing duplicate impl detection after generated impl
  insertion.
- Better diagnostics can be added by a derive pre-pass that scans sibling
  `Stmt::Impl` targets before insertion.

## Standard Library Migration

After derive works:

1. Change:

   ```hern
   type Option('a) = Some('a) | None
   type Result('a, 'e) = Ok('a) | Err('e)
   type Ordering = LT | EQ | GT
   ```

   to:

   ```hern
   #[derive(Eq, ToString)]
   type Option('a) = Some('a) | None

   #[derive(Eq, ToString)]
   type Result('a, 'e) = Ok('a) | Err('e)

   #[derive(Eq, ToString)]
   type Ordering = LT | EQ | GT
   ```

2. Remove handwritten `ToString for Option`, `ToString for Result`,
   `ToString for Ordering`, and concrete `Eq for Option(int)` only after tests
   prove generic derived impls resolve correctly.
3. Upgrade `assert_eq`:

   ```hern
   fn assert_eq(lhs: 'a, rhs: 'a) -> ()
   where 'a: Eq + ToString
   {
     assert(
       lhs == rhs,
       "assert_eq failed: " <> ToString::to_string(lhs) <> " != " <> ToString::to_string(rhs)
     )
   }
   ```

4. Add `assert_ne` using the same bounds.

## Test Plan

Parser tests:

- accepts `#[derive(Eq)] type T = A | B`;
- accepts `#[derive(Eq, ToString)] type T('a) = A('a) | B`;
- rejects derive on `fn`;
- rejects derive on `test` functions;
- rejects unknown derive trait;
- rejects duplicate derive trait;
- rejects derive on aliases for v1.

Derive lowering tests:

- `Option('a)` generates two impls for `Eq` and `ToString`;
- generated impl targets are `Option('a)`, not `Option`;
- generated bounds mention only type params used in payloads;
- nullary-only types generate no bounds.

Inference/codegen integration tests:

- derived `Eq` works for nullary enum values;
- derived `Eq` works for one-payload enum values;
- derived `ToString` prints `None`, `Some(1)`, `Ok(1)`, `Err(error)`;
- derived generic impl resolves for `Option(int)`;
- derived `Eq` fails cleanly if payload type lacks `Eq`;
- derived `ToString` fails cleanly if payload type lacks `ToString`;
- manual impl plus derive conflicts.

LSP/recovering tests:

- unknown derive name reports a diagnostic without dropping the rest of the file;
- hover/completion still work after a valid derive;
- error in a derived impl points at the derive attribute, not line 0/column 0.

Regression tests:

- full `cargo test -p hern-core`;
- full `cargo test -p hern-lsp`;
- full `cargo test -p hern`;
- full `python3 tests/run.py`.

## Implementation Phases

### Phase 1: Generic Impl Resolution Safety Net

- Add failing/passing tests for handwritten generic `Eq for Box('a)`.
- Fix applied generic impl resolution if those tests fail.
- Do not start derive lowering until this is green.

### Phase 2: AST And Parser

- Add `DeriveAttr`, `DeriveTrait`, and `TypeDef::derives`.
- Parse `#[derive(...)]` before type declarations.
- Preserve existing `#[test]` restrictions.
- Add parser unit tests.

### Phase 3: Derive Lowering Module

- Add `hern-core/src/derive.rs`.
- Implement `DeriveInput` extraction.
- Implement shared AST builders.
- Implement `derive_eq`.
- Implement `derive_to_string`.
- Insert generated impls after each type declaration.

### Phase 4: Pipeline Integration

- Run derive expansion after import resolution and before reassociation.
- Add fail-fast and recovering diagnostics.
- Ensure prelude analysis goes through derive expansion.

### Phase 5: Diagnostics And Generated Markers

- Add generated marker metadata to `ImplDef`.
- Remap synthetic generated errors to derive spans.
- Avoid exposing generated impls as normal document symbols.

### Phase 6: Std Migration

- Replace handwritten std impls with derives where tests prove equivalence.
- Upgrade `assert_eq` to include stringified values.
- Add `assert_ne`.

### Phase 7: Full Verification

- Run core, LSP, CLI, and integration tests.
- Add one `hern test` fixture that uses derived `Eq` and `ToString` in
  `assert_eq`.
- Review generated Lua for simple derived examples to make sure no test-only or
  synthetic names leak in surprising ways.

## Non-Goals For V1

- Derive customization attributes such as skipping fields or custom printers.
- Deriving for type aliases.
- Deriving for records if records are not yet nominal declarations.
- Standalone derives separate from the type declaration.
- User-defined derive plugins.
- A Rust-like proc macro system.
- Pretty-print stability guarantees beyond the documented structural format.

## Design Decision Summary

- Use `#[derive(Eq, ToString)]` syntax.
- Store derives on `TypeDef`.
- Lower derives to ordinary `Stmt::Impl`.
- Share a single type-shape walker between `Eq` and `ToString`.
- Insert generated impls before reassociation and inference.
- Require generic impl resolution to be correct before using derive in std.
- Treat `ToString` deriving as explicit, structural, user-requested output.
