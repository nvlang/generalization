# Generalization linter

A Lean 4 + Mathlib linter (BSc thesis) that flags declarations whose typeclass
assumptions can be **weakened** — e.g. suggesting `[Monoid G]` where `[Group G]`
was assumed. It models the typeclass hierarchy as a DAG and computes the weakest
class (the "meet") that a declaration's proof actually uses.

*This file is the single source of truth for agent instructions; `CLAUDE.md` is
a symlink to it.*

## Rules for agents

This is a rewrite of the Lean project from `../code/project/`. All code and
documentation in `./src/` will be written and edited exclusively by me, a human.

You MUST NOT create, delete, or edit any file in the `./src/` directory.

You MAY create, delete, or edit any file in the `./tests/` directory. The
purpose of the `./tests/` directory is to contain test files that support this
rewrite in the style of test-driven development (TDD). Tests in the `./tests/`
directory MAY be informed by insights gained from work done in the
`../code/project/` directory. However, tests should not impose
implementation-specific behavior from the `../code/project/` project on this
rewrite.

Tests added by a Claude Opus 4.8 agent MUST be audited, efficiently but
effectively, by a separate, independent Claude Opus 4.8 agent to ensure the
added or modified tests make sense mathematically and verify that after applying
the expected suggestions, declarations would still type-check in the context
(Lean file and location within it) in which they resided.

Tests added by a Fable 5 agent SHOULD NOT be audited by a separate agent.

Agents using a Claude model that is weaker than Opus 4.8 (for example, Opus 4.7,
Opus 4.6, Sonnet 4.6, or Haiku 4.5) MUST NOT create, delete, or edit any file in
this project, not even test files. These weaker models may only read files in
this project.

## Commands

```bash
lake exe cache get   # fetch prebuilt Mathlib first — avoids recompiling all of Mathlib
lake build           # build the GeneralizationLinter library
lake env lean <file> # elaborate one file and print its #eval / logInfo output
```

- Tests live in `tests/` and are run file-by-file, e.g. `lake env lean tests/Foo.lean`.
  No `lake test` target is wired up yet.
- `src/Helpers/Environment.lean` is a runnable scratch file showing how to explore
  Mathlib's environment via `lake env lean`.

## Toolchain & conventions

- Lean `v4.31.0-rc2` (`lean-toolchain`) + Mathlib `v4.31.0-rc2` (`lakefile.toml`).
- Source uses the **new Lean module system**: files open with `module` and use
  `public import` / `public def` (see `src/Helpers/ClassApp.lean`).
- `relaxedAutoImplicit` is **off** (`lakefile.toml`) — declare implicit binders
  explicitly.
- New `.lean` files (including tests) carry a Mathlib-style Apache-2.0 copyright
  header matching the existing `src/` files.
