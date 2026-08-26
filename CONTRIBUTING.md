# Contributing to LuaR

LuaR is a compiler written in Rust. `.internal/SPEC.md` defines the language;
the compiler exists to match it.

## Getting set up

You need a Rust toolchain (stable, 1.85 or newer) and nothing else.

```sh
git clone https://github.com/OMouta/luaR
cd luaR
cargo build
```

## Running the tests

There are two suites, and they answer different questions.

**The conformance suite** is the one that matters. Each test is a LuaR program
under `tests/conformance/` plus the behavior it expects, and every test cites
the spec section it enforces.

```sh
cargo run -p luarc -- test              # the whole suite
cargo run -p luarc -- test strings      # the tests whose path contains "strings"
```

**The Rust tests** cover the compiler's own internals: the precedence table,
the lexer's maximal munch, error recovery, the conformance runner itself.

```sh
cargo test --workspace
```

Both run in CI, along with the checks that gate a merge:

```sh
cargo fmt --all --check
cargo clippy --workspace --all-targets -- -D warnings
```

## The command line

`luarc` is the compiler's front door. It reads files, runs the suite, and says
what the suite does not reach.

```sh
cargo run -p luarc -- check path/to/file.luar   # report what is wrong with it
cargo run -p luarc -- test [filter]             # run the conformance suite
cargo run -p luarc -- coverage                  # spec sections with no test
cargo run -p luarc -- run path/to/file.luar     # not yet: there is no backend
```

`check` reads as far as the compiler currently goes, which is the syntax tree.
A program it accepts is one that lexes and parses; every stage added after this
narrows what acceptance means.

## Writing a test

A test is a LuaR program and its expected observable behavior, stated in a
directive header:

```lua
--- expect: compile-error
--- code: LR0114
--- span: 2:15
--- spec: §11.1
local ratio = 10 / 3
```

- `expect` is `compile-ok`, `compile-error`, or `run`.
- `code` and `span` are required for `compile-error`, and are what the test
  matches on. Never match on message text: wording is not normative (§80).
- `spec` cites the section the test enforces, and may be repeated. Without it
  a test enforces nothing but itself.
- `run` tests need a backend. Write them as features arrive and let them sit
  skipped, so the day the backend works the suite says how much of the
  language does.

Put the file under `tests/conformance/<area>/<name>.luar`. It is picked up by
being there.

## Rules that are not style

**Changing an expectation requires changing the spec in the same commit.** If
the spec did not change, the expectation was right and the compiler is wrong.
This is the rule that keeps a failing test from being edited into a passing
one.

**Never delete or weaken a test to make a build pass.** A test that is
genuinely wrong is wrong because the spec says something different. Cite that,
or leave it failing.

**If the spec turns out to be wrong or ambiguous, fix the spec first, in its
own commit, and say so.** Implementing around a bad rule leaves two sources of
truth that disagree.

**Every rule the compiler enforces has a diagnostic code.** Codes live in
`crates/luar-diagnostics/src/codes.rs`, one per rule, cited to the section that
states it. A number is never reused once assigned, because build logs and
recorded expectations still refer to it.

## The crates

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

Stages after the parser are not built yet. `luarc check` reaches exactly as far
as the compiler does.
