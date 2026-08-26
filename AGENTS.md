# AGENTS.md

LuaR is a compiled language. This repo is its compiler, written in Rust, and the conformance suite that decides whether the compiler matches the language.

`.internal/SPEC.md` is the language, and it is normative. Every rule the compiler enforces cites the section that states it: in the diagnostic registry, in the test that produces it, and in the commit that changes it.

`CONTRIBUTING.md` has the commands, the test file format, and what each crate holds. Read it first. This file is the part that is easy to get wrong.

## The spec is the authority

The compiler is an attempt at the spec. When the two disagree, the spec is right.

When the spec is wrong, ambiguous, or silent on something you need, change the spec in its own commit, before the code that depends on it, and say so in your summary. A compiler rule with no section behind it is a rule nobody agreed to, and a test for that rule proves only that the compiler agrees with itself.

## A failing test makes the compiler the suspect

Work out which of three things is true before you touch anything:

1. **The compiler is wrong.** Fix the compiler. This is the usual answer.
2. **The program was never valid.** A test program can be invalid under a rule the compiler only just learned to enforce, so landing a stage routinely fails tests that passed the day before. Fix the program, keep its expectation and its subject intact, and name the section that makes it invalid.
3. **The spec is wrong.** Change the spec in its own commit, then the expectation.

Two branches change a test, and both start from a spec section that says the program was wrong. Absent that section, the compiler is what changes.

When a compiler defect surfaces while you are working on something else, fix the defect or leave the test failing with its citation. Rewriting the program until the suite goes green buries the defect and makes the suite report success on exactly the thing it was written to catch.

## Tests

- A test is a LuaR program plus its observable behavior: an exit code, stdout, or a diagnostic. Not a token stream, an AST node, or an internal function's return.
- Every test cites the spec sections it enforces. No citation, no test.
- A negative test matches a diagnostic code and a source span. Wording is not normative (§80) and gets reworded without warning.
- Unit tests are for units that are themselves the contract: integer overflow helpers, UTF-8 boundary math, the range arithmetic in bounds-check elimination. Everything else is a conformance test running the real pipeline, with no mocked stages.
- Write `run` tests as the features arrive. They report as skipped until the backend exists, and the day it lands the suite says how much of the language works.
- `luarc coverage` lists the spec sections no test cites. That list is the backlog.

## Adding a rule

1. Find the section that states it.
2. Add a code to `crates/luar-diagnostics/src/codes.rs`: the next number, ascending, cited to that section. A retired number stays retired, because build logs and recorded expectations still name it.
3. Enforce it.
4. Write the conformance test that produces the code, and keep a test that stays accepted where the rule does not apply.
5. Run the whole suite and expect casualties. Each one goes through the three branches above.

## Before committing

```sh
cargo fmt --all
cargo clippy --workspace --all-targets -- -D warnings
cargo test --workspace
```

CI runs the same three, and a clippy warning fails the build.

Commit in small units, one coherent change each, with a short direct subject line and no trailers. A spec change commits alone.
