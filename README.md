# Automated Theorem Generalization in Lean

This project's primary goal is to contribute a typeclass linter to
[Mathlib](https://github.com/leanprover-community/mathlib4) which flage overly strong typeclass
hypotheses and suggests weakenings.

The source code is heavily commented, as this was both important for me to ensure I understood all
the code, and likewise will be equally important for me to understand the code again in the future
after I inevitably forget how it worked. Whatever version of this project may ultimately end up in a
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

There's a few additional `generalizeTypeclasses.*` options available, and a universe linter under
`linter.generalizeUniverses` (off by default).


### Implementation

I used `doc-gen4` to generate a documentation website automatically from the docstrings in the
source code. This website is available at %TODO.


## Tool and computational resource disclosure

I used generative artificial intelligence (AI) for this project, primarily Anthropic's Claude
Fable 5, Opus 4.8, Opus 4.7, and Opus 4.6 models.
