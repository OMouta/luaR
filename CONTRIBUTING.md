# Contributing

LuaR is a compiler written in Rust. `.internal/SPEC.md` defines the language.
When the spec and the compiler disagree, the spec is right until someone
changes it, and changing it is its own commit.

## Setup

Rust 1.85 or newer builds everything.

```sh
git clone https://github.com/OMouta/luaR
cd luaR
cargo build
```

If you have [Rokit](https://github.com/rojo-rbx/rokit), `rokit install` adds
[Lute](https://github.com/luau-lang/lute), which runs the task runner in
`luar.luau`. It only shortens the cargo commands, so skip it if you would
rather type them out.

## Tests

Two suites.

The conformance suite is LuaR programs under `tests/conformance/`, each one
carrying the behavior it expects and the spec section it enforces. It runs in
about 80ms, so run it constantly.

```sh
lute luar test                          # cargo run -q -p luarc -- test
lute luar test strings                  # only paths containing "strings"
```

The Rust tests cover the compiler's internals: the precedence table, maximal
munch in the lexer, error recovery, the conformance runner itself.

```sh
lute luar unit                          # cargo test --workspace
```

CI runs both, plus format and lint. Clippy warnings fail the build. One command
runs the lot in the same order, which is what to do before pushing.

```sh
lute luar ci
```

## Commands

Each one is a cargo command underneath. `lute luar` with no argument lists
them.

| Task | Cargo |
| --- | --- |
| `lute luar check file.luar` | `cargo run -q -p luarc -- check file.luar` |
| `lute luar test [filter]` | `cargo run -q -p luarc -- test [filter]` |
| `lute luar coverage` | `cargo run -q -p luarc -- coverage` |
| `lute luar run file.luar` | `cargo run -q -p luarc -- run file.luar` |
| `lute luar build` | `cargo build --workspace` |
| `lute luar unit` | `cargo test --workspace` |
| `lute luar fmt` | `cargo fmt --all` |
| `lute luar lint` | `cargo clippy --workspace --all-targets -- -D warnings` |
| `lute luar ci` | format, lint, unit tests, conformance |

`check` reaches the syntax tree and stops, because that is where the compiler
stops. It will reject more programs as name resolution and type checking land,
so a file that passes today may not later. `run` exits 2, because there is no
backend.

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

`expect` is `compile-ok`, `compile-error`, or `run`.

`compile-error` needs `code` and `span`, and they are the only things it
matches on. Never match message text. LR80 makes wording non-normative, so
messages get reworded without warning and a test that reads them breaks for no
reason.

`spec` may repeat. A test that cites nothing checks only that the compiler
agrees with itself.

`run` needs a backend, so it reports as skipped today. Write them anyway. When
the backend lands, the suite immediately says how much of the language works.

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
| `luar-lir` | The typed SSA the optimizer works on |
| `luar-codegen` | Machine code |
| `luar-driver` | One compilation, end to end |
| `luar-conformance` | The suite runner and the coverage report |
| `luarc` | The command line |

Everything after `luar-parser` is empty.
