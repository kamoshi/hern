# Hern Macro Execution Model

Status: accepted direction for production macros.

Hern macros run in an isolated compiler-owned comptime runtime. Macro code is
Hern code, but it executes in a separate phase-1 world with a pure API, explicit
resource limits, and no ambient access to the host machine.

## Goals

- Macros should feel like ordinary Hern where possible.
- Macro expansion must be deterministic.
- Macro execution must not have filesystem, network, process, clock, random, or
  environment access by default.
- Macro authors transform `Syntax -> MacroResult(Syntax)`.
- Expanded output is parsed and typechecked by the ordinary compiler pipeline.
- The public macro API is syntax objects, not the compiler's internal typed AST.

## Phase Model

Hern has two initial phases:

- phase 0: ordinary runtime Hern code
- phase 1: macro/comptime Hern code

Macro definitions are phase-1 declarations. A macro definition has the shape:

```hern
macro name(input: Syntax) -> MacroResult(Syntax) {
  ...
}
```

Macro calls are phase-0 expansion sites:

```hern
name!(...)
```

The compiler contract is:

1. Parse the source program.
2. Collect macro definitions.
3. Typecheck macro bodies as phase-1 Hern.
4. Execute macro calls in the isolated comptime runtime.
5. Parse expanded `Syntax` back as ordinary Hern source.
6. Run the normal resolve, reassociate, typecheck, and codegen pipeline.

Macro expansion input is untyped syntax. Macro expansion output is also syntax,
then it is parsed and typechecked normally. The macro system must not inject
compiler-internal AST nodes as a stable public API.

## Runtime Isolation

The comptime runtime has no ambient authority. Macro code cannot:

- read or write files
- access the network
- spawn processes
- inspect environment variables
- inspect the current directory
- read wall-clock time
- use randomness
- call runtime `extern`s
- dynamically load host modules
- access compiler internals except through explicit stable APIs

Phase-1 code can use only:

- macro input `Syntax`
- syntax quotes and syntax patterns
- pure Hern values and control flow supported by the comptime runtime
- macro-local bindings
- phase-1 helper functions
- whitelisted compiler-provided syntax APIs

Future capabilities must be explicit and auditable. They are not part of the
production v1 macro model.

## Chosen Execution Path

The current implementation uses a restricted Rust comptime evaluator. That is a
bootstrap implementation, not the long-term semantic strategy.

The production path is:

1. Typecheck macro definitions as phase-1 Hern.
2. Lower the checked macro body to a shared, typed Hern core IR.
3. Execute that IR in a deterministic compile-time host.
4. Marshal only stable macro values across the host boundary, especially
   `Syntax`, arrays, strings, booleans, numbers, `Option`, `Result`, and
   `MacroError`.

This keeps macro execution Hern-native while avoiding an endless pile of
handwritten `ExprKind` evaluator branches. Runtime Hern and phase-1 Hern should
share lowering semantics wherever possible; the phase-1 host decides which
effects and operations are available.

Lua chunks are not the preferred production substrate unless they are sealed into
a deterministic VM with no host libraries and no ambient IO. Rust-linked
procedural macro plugins and arbitrary host-language escape hatches are not part
of production v1.

## Allowed Phase-1 Effects

Production v1 phase-1 code may perform:

- pure computation
- local lexical binding and local mutation supported by the macro IR
- syntax construction through quotes/templates
- syntax pattern matching
- deterministic string, array, option, result, and syntax helper calls
- returning `Ok(Syntax)` or `Err(MacroError)`

Production v1 phase-1 code may not perform:

- filesystem IO
- network IO
- process IO
- environment-variable reads
- current-directory reads
- wall-clock reads
- randomness
- runtime `extern` calls
- mutation of imported or global runtime state

## Resource Limits

Macro execution is bounded by `MacroExecutionOptions`:

- `max_expansions`: maximum macro call expansions in one program expansion pass.
  This catches recursive expansions such as a macro expanding into another macro
  call forever.
- `max_eval_steps`: maximum evaluator steps inside one macro invocation.
- `max_output_syntax_nodes`: maximum size of the returned syntax tree.
- `max_call_depth`: maximum macro-phase helper call depth inside one macro
  invocation.
- `max_generated_source_bytes`: maximum normalized source length before
  parse-back.

Hitting any limit is a compiler diagnostic, not a crash. Tests may override the
limits through `expand_macros_with_options`; production callers should use the
defaults unless they intentionally expose a compiler setting.

## Prelude Boundary

The long-term macro prelude should be separate from the runtime prelude:

```text
std/macro.hern
```

It should contain pure helpers for:

- `Syntax`
- arrays
- strings
- `Option`
- `Result`
- `MacroError`
- fresh identifiers
- diagnostic construction

Runtime-only values and externs are not visible in phase 1 unless a future
capability model explicitly permits them.

## Security Contract

Compiling a package with macros should not grant that package arbitrary access to
the developer's machine. The compiler may still treat macro code as trusted
source for language-level behavior, but the execution substrate must enforce:

- no ambient IO
- no host imports
- deterministic evaluation
- bounded resources
- stable diagnostics on failure

This model intentionally avoids Template Haskell-style arbitrary compile-time IO,
keeps the macro surface more Hern-native than Scala/JVM bytecode execution, and
uses Racket's phase-separation lesson without requiring a full phase tower on day
one.
