# Generalization linter

A Lean 4 + Mathlib linter (BSc thesis) that flags declarations whose typeclass
assumptions can be **weakened** — e.g. suggesting `[Monoid G]` where `[Group G]`
was assumed. It models the typeclass hierarchy as a DAG and computes the weakest
class (the "meet") that a declaration's proof actually uses.

## Rules for agents

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

## Guidelines

- For each non-trivial claim you make, indicate how confident you feel about the correctness of said
  claim, and why you feel that way.
- Principled approaches are preferred. Avoid patchworks of ad hoc fixes whenever possible.
- Codebase complexity and size should be kept minimal whenever possible.
- For the linter's behavior, soundness must always remain guaranteed, while recall should be
  maximized.

## Commands

```bash
lake exe cache get   # fetch prebuilt Mathlib first — avoids recompiling all of Mathlib
lake build           # build the GeneralizationLinter library
lake env lean <file> # elaborate one file and print its #eval / logInfo output
```

- Tests live in `tests/` and are run file-by-file, e.g. `lake env lean tests/Foo.lean`.
  No `lake test` target is wired up yet.

## Toolchain & conventions

- Lean `v4.32.0` (`lean-toolchain`) + Mathlib `v4.32.0` (`lakefile.toml`).
- Source uses the **new Lean module system**: files open with `module` and use
  `public import` / `public def` (see `GeneralizationLinter/Helpers/ClassApp.lean`).
- `relaxedAutoImplicit` is **off** (`lakefile.toml`) — declare implicit binders
  explicitly.
- New `.lean` files (including tests) carry a Mathlib-style Apache-2.0 copyright
  header matching the existing `GeneralizationLinter/` files.
