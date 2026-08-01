# Automated Theorem Generalization in Lean

This project's primary goal is to contribute a typeclass linter to
[Mathlib](https://github.com/leanprover-community/mathlib4) which flags overly strong typeclass
hypotheses and suggests weakenings.

The source code is heavily commented. Whatever version of this project may ultimately end up in a
Mathlib pull request, its comments/docstrings will be condensed and adapted to comply with Mathlib's
style guide.

## Documentation

### Installation and Usage

Currently, the only way to run the linter is to download/clone this repository and import the
project locally. Hopefully, I'll be able to submit a PR for this linter to Mathlib within the coming
weeks or months. Should that PR be rejected, I'll probably just submit the project to
[Reservoir](https://reservoir.lean-lang.org/).

The linter "initializes" itself on import, so any file which imports the linter (even if just
indirectly) has access to it. To turn it on, you can set `linter.generalizeTypeclasses` to `true`
(it's off by default):

```lean4
set_option linter.generalizeTypeclasses true
```

There's a few additional options available:

- `generalizeTypeclasses.splitPolicy : String` (`"forbid"` by default): controls whether typeclass
  weakenings that would involve splitting a single hypothesis into two weaker ones should be
  suggested. Suggested weakenings that split typeclass hypotheses can violate diamond coherence.
  Measures are in place to significantly reduce the frequency of such false  positives, but they do
  not eliminate them, which is why this option is set to `"forbid"` by default. Setting this option
  to `"allow"` will make the linter suggest splitting a typeclass hypothesis only if it could not be
  weakened otherwise. Setting this option to `"prefer"` will make the linter always suggest the most
  general weakening, even if that means suggesting a split where a less general non-splitting
  weakening would be available
- `generalizeTypeclasses.targetImplicit : Bool` (`true` by default): controls whether implicit and
  strict implicit binders should also be scanned for potential weakenings. Instance implicit binders
  are always scanned if the linter is active.
- `generalizeTypeclasses.perCandidateHeartbeats : Nat` (`4_000_000` by default): per-candidate
  heartbeat budget for the linter's analysis. If $n$ is the number of targeted binders in a given
  declaration and $m$ is the ambient maxHeartbeats, then, for each declaration, the linter will take
  at most $(n + 2) \cdot \min(\texttt{perCandidateHeartbeats}, m)$ heartbeats.
- `generalizeTypeclasses.acceptOmits : Bool` (`false` by default): whether declarations within `omit
  … in` commands or within sections with any `omit …` commands should be analyzed by the linter.
  Default: `false`. **Warning:** For these declarations, the linter cannot guarantee that its
  suggestions will elaborate.

### Implementation

For implementation detail, you can consult the [documentation
website](https://nvlang.github.io/generalization/docs/) that was generated automatically from the docstrings in the source code using `doc-gen4`.


## Tool and computational resource disclosure

I used generative artificial intelligence (AI) while working on this project, primarily Anthropic's
Claude Fable 5, Opus 5, Opus 4.8, Opus 4.7, and Opus 4.6 models.
