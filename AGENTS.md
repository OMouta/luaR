# AGENTS.md

LuaR is a compiled language and this repo is its compiler, written in Rust. The conformance suite under `tests/conformance/` decides whether the compiler matches the language.

`.internal/SPEC.md` is the language. Every rule the compiler enforces cites the section that states it, and so does the test for that rule.

`CONTRIBUTING.md` has the commands, the test file format, and what each crate holds. Read it first.

## Say less

Do not explain the reason behind what you changed. Not in comments, not in config files, not in docs. State the rule or the behavior and stop.

Do not tell the reader what they already know. This repo is read by people who write compilers in Rust.

A comment earns its place by saying something the code cannot: a spec section, an invariant, a constraint that is not visible locally. Delete the rest.

Deletion is the best edit.

## The spec wins

When the compiler and the spec disagree, the spec is right.

When the spec is wrong, ambiguous, or silent on something you need, change the spec first, in its own commit, and say so in your summary.

## When a test fails

Decide which of three things is true before you change anything.

1. **The compiler is wrong.** Fix the compiler. This is the usual answer.
2. **The program was never valid.** Fix the program, keep its expectation and its subject, and cite the section that makes it invalid.
3. **The spec is wrong.** Change the spec in its own commit, then the expectation.

Two of those change a test, and both need a spec section saying the program was wrong. Without one, fix the compiler.

Finding a compiler bug while working on something else does not change this. Fix the bug, or leave the test failing and cite the section.

## Tests

- A test is a LuaR program and its observable behavior: an exit code, stdout, or a diagnostic. Never a token stream, an AST node, or what some internal function returned.
- Every test cites the spec sections it enforces. No citation, no test.
- A negative test matches a diagnostic code and a source span, never message wording (LR80).
- Write conformance tests by default. Save unit tests for code that is itself the contract: integer overflow helpers, UTF-8 boundary math, the range arithmetic in bounds-check elimination. Every test runs the real pipeline, never a mocked stage.
- Write `run` tests as features arrive.
- `luarc coverage` lists the spec sections no test cites. Start there when you want work.

## Adding a rule

1. Find the section that states it.
2. Add a code to `crates/luar-diagnostics/src/codes.rs`, the next number up, cited to that section. Retired numbers stay retired.
3. Enforce it.
4. Write a test that produces the code, and one that stays accepted where the rule does not apply.
5. Run the whole suite. Work each failure through the three branches above.

## The standard library

`std/` holds it, one LuaR module per file, compiled into `luarc`. `std/mem` is `std/mem.luar`. A collection or `Result` method written in LuaR lives in `std/prelude.luar`; the compiler keeps only what has no LuaR spelling.

Native code enters through `@extern("c")` to libc (LR46). An operation with no LuaR spelling is a bodiless `@intrinsic` declaration in `std/` (LR60): one over ABI-representable values is a runtime symbol `luar_<name>` in `luar-codegen`, and one whose lowering depends on types is lowered in `luar-lir`. Predeclared names (LR54.1) are the compiler's. The compiler recognizes no standard library function by name, and no module lives in Rust.

## Before committing

```sh
cargo fmt --all
cargo clippy --workspace --all-targets -- -D warnings
cargo test --workspace
stylua luar.luau
```

CI runs those four. A clippy warning fails the build.

Keep commits small, one change each, with a short plain subject line and no trailers. A spec change commits alone.
