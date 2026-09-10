# Contributing

LuaR is a compiler written in Rust. `.internal/SPEC.md` defines the language
and `.internal/STD-SPEC.md` the standard library.
When the spec and the compiler disagree, the spec is right until someone
changes it, and changing it is its own commit.

## Setup

```sh
git clone https://github.com/OMouta/luaR
cd luaR
cargo build
```

`cargo luar` runs the task runner in `luar.luar` through the compiler.

## Tests

Two suites.

The conformance suite is LuaR programs under `tests/conformance/`, each one
carrying the behavior it expects and the spec section it enforces. A test that
runs a program builds and links it, so the suite takes a few seconds.

```sh
cargo luar test
cargo luar test strings                 # only paths containing "strings"
```

The Rust tests cover the compiler's internals: the precedence table, maximal
munch in the lexer, error recovery, the conformance runner itself.

```sh
cargo luar unit                         # cargo test --workspace
```

CI runs both, plus format and lint. Clippy warnings fail the build. One command
runs the lot in the same order. Run it before pushing.

```sh
cargo luar ci
```

## Commands

Each one is a cargo command underneath. `cargo luar` with no argument lists
them.

| Task | Cargo |
| --- | --- |
| `cargo luar check file.luar` | `cargo run -q -p luarc -- check file.luar` |
| API documentation as Markdown | `cargo run -q -p luarc -- doc file.luar` |
| `cargo luar test [filter]` | `cargo run -q -p luar-conformance --features tools --bin conformance -- [filter]` |
| `cargo luar coverage` | `cargo run -q -p luar-conformance --features tools --bin coverage` |
| `cargo luar run file.luar [args]` | `cargo run -q -p luarc -- run file.luar [args]` |
| `cargo luar lir file.luar` | `cargo run -q -p luarc -- lir file.luar` |
| `cargo luar build` | `cargo build --workspace` |
| `cargo luar unit` | `cargo test --workspace` |
| `cargo luar fmt` | `cargo fmt --all` |
| `cargo luar lint` | `cargo clippy --workspace --all-targets --all-features -- -D warnings` |
| `cargo luar ci` | format, lint, unit tests, conformance |

## Writing a conformance test

Put a `.luar` file under `tests/conformance/<area>/`. The runner walks the
directory, so there is no list to add it to.

```lua
--- expect: compile-error
--- code: LR0114
--- span: 2:15
--- spec: LR11.1
local ratio = 10 / 3
```

`expect` is `compile-ok`, `compile-error`, `run`, or `doc`.

`expect: doc` checks generated API Markdown against `stdout` after type checking.

`compile-error` needs `code` and `span`, and they are the only things it
matches on. Never match message text. LR80 makes wording non-normative, so
messages get reworded without warning and a test that reads them breaks for no
reason.

`spec` may repeat. Language sections are `LR…`, standard-library sections
`STD…`. A test that cites nothing checks only that the compiler
agrees with itself.

`format: true` compares formatter output with a sibling `.formatted` file,
checks idempotence, then compiles or runs the formatted source.

`run` builds, links, and executes the program. It reports as skipped when
lowering or code generation does not cover the program yet.

A `run` program starts in the directory holding its test, so a fixture beside
the test is opened by name.

## Rules

Changing what a test expects means changing the spec in the same commit. If the
spec did not change, the expectation was right and the compiler is wrong.

Do not delete or weaken a test to get a green build.

Found a spec bug? Fix the spec first, in its own commit, then write the code.

Every rule the compiler enforces has a code in
`crates/luar-diagnostics/src/codes.rs`, cited to the section that states it.
Numbers are never reused. Old build logs and recorded expectations still refer
to them.

## Crates

| Crate | What it does |
| --- | --- |
| `luar-diagnostics` | Diagnostics, spans, source maps, the code registry |
| `luar-lexer` | Source text to tokens |
| `luar-ast` | The syntax tree |
| `luar-parser` | Tokens to the syntax tree |
| `luar-sema` | Name resolution and type checking |
| `luar-lir` | The typed SSA, lowering into it, and the passes over it |
| `luar-codegen` | Machine code |
| `luar-driver` | One compilation, end to end |
| `luar-conformance` | The suite runner and the coverage report |
| `luarc` | The command line |

`std/` is the standard library: LuaR source, one module per file, compiled into `luarc`.

`luar-codegen` emits native object files and a subset of WebAssembly.
`luar-driver` links native executables. `luarc lir file.luar` prints the lowered
program and anything lowering could not cover.
