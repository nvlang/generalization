# Generalization linter

A Lean 4 linter for Mathlib that flags theorems with overly strong (type)class hypotheses and
suggests verified weakenings. It models the class hierarchy as a directed graph, computes its
condensation, collects the set of requirements imposed on each class binder by the proof, computes
the least upper bound (aka. the "join", or supremum) of these requirements within the class graph,
verifies these weakening candidates, and then, if successful, emits (i.e., logs) them as
suggestions.

## Rules for agents

Agents MUST NOT create, delete, or edit any file in the main worktree, MUST NOT commit to `main`,
and MUST NOT push any changes to remotes.

Agents using a Claude model that is weaker than Opus 5 (for example, Opus 4.8, Opus 4.7, Opus 4.6,
Sonnet 4.6, or Haiku 4.5) MUST NOT create, delete, or edit any file in this project, not even test
files. These weaker models may only read files in this project.

## Guidelines

- For each non-trivial claim you make, indicate how confident you feel about the correctness of said
  claim, and why you feel that way.
- Principled approaches are preferred. Avoid patchworks of ad hoc fixes whenever possible.
- Codebase complexity and size should be kept minimal whenever possible.
- For the linter's behavior, soundness must always remain guaranteed, while recall should be
  maximized.

## Commands

- Use the Lean LSP MCP for small probes.
- Tests live in `tests/` and are run file-by-file, e.g. `lake env lean tests/Foo.lean`.
  No `lake test` target is wired up yet.

## Toolchain & conventions

- Lean `v4.32.1` (`lean-toolchain`) + Mathlib `v4.32.1` (`lakefile.toml`).
- Source uses the new Lean module system: files open with `module` and use `public import` /
  `public def`.
- `relaxedAutoImplicit` is off (`lakefile.toml`): declare implicit binders explicitly.
- New `.lean` files (including tests) carry a Mathlib-style Apache-2.0 copyright header matching the
  existing `GeneralizationLinter/` files.
