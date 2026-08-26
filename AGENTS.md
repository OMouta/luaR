# AGENTS.md

LuaR is a compiled language, and this repo is its compiler, written in Rust. The conformance suite under `tests/conformance/` decides whether the compiler matches the language.

`.internal/SPEC.md` is the language. Every rule the compiler enforces cites the section that states it, and so does the test for that rule.

`CONTRIBUTING.md` has the commands, the test file format, and what each crate holds. Read it first.

## The spec wins

When the compiler and the spec disagree, the spec is right.

When the spec is wrong, ambiguous, or silent on something you need, change the spec first, in its own commit, and say so in your summary. A rule with no section behind it is one nobody agreed to, and its test proves only that the compiler agrees with itself.

## When a test fails

Decide which of three things is true before you change anything.

1. **The compiler is wrong.** Fix the compiler. This is the usual answer.
2. **The program was never valid.** Landing a new stage routinely fails tests that passed the day before, because the compiler only just learned to reject them. Fix the program, keep its expectation and its subject, and cite the section that makes it invalid.
3. **The spec is wrong.** Change the spec in its own commit, then the expectation.

Two of those change a test, and both need a spec section saying the program was wrong. Without one, fix the compiler.

Finding a compiler bug while working on something else does not change this. Fix the bug, or leave the test failing and cite the section. Rewriting the program until the suite goes green hides the bug, and the suite then reports success on the thing it was written to catch.

## Tests

- A test is a LuaR program and its observable behavior: an exit code, stdout, or a diagnostic. Never a token stream, an AST node, or what some internal function returned.
- Every test cites the spec sections it enforces. No citation, no test.
- A negative test matches a diagnostic code and a source span. §80 leaves wording open, so anyone may reword a message, and a test that reads one breaks for no reason.
- Write conformance tests by default. Save unit tests for code that is itself the contract: integer overflow helpers, UTF-8 boundary math, the range arithmetic in bounds-check elimination. Every test runs the real pipeline, never a mocked stage.
- Write `run` tests as features arrive. They skip until the backend exists, and the day it lands the suite reports how much of the language works.
- `luarc coverage` lists the spec sections no test cites. Start there when you want work.

## Adding a rule

1. Find the section that states it.
2. Add a code to `crates/luar-diagnostics/src/codes.rs`, the next number up, cited to that section. Retired numbers stay retired, because old build logs and recorded expectations still name them.
3. Enforce it.
4. Write a test that produces the code, and one that stays accepted where the rule does not apply.
5. Run the whole suite. Expect failures, and work each one through the three branches above.

## Before committing

```sh
cargo fmt --all
cargo clippy --workspace --all-targets -- -D warnings
cargo test --workspace
```

CI runs those three. A clippy warning fails the build.

Keep commits small, one change each, with a short plain subject line and no trailers. A spec change commits alone.
