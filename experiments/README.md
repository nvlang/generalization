# Reproducing the sweep

> [!NOTE] 
> **Disclosure:** This README was written by AI.

```bash
docker build --build-arg GL_REVISION="$(git rev-parse HEAD)" -t gl-repro -f experiments/Dockerfile .
mkdir -p out && docker run --rm -v "$PWD/out:/out" gl-repro
```

Build from the repository root: the context needs `lean-toolchain`, `lakefile.toml`,
`lake-manifest.json`, `GeneralizationLinter.lean`, `GeneralizationLinter/`, `experiments/run.py`, and the
root `.dockerignore`. `GL_REVISION` ties the output to a commit; without it `meta.json` records
`linter_revision: "unknown"`. The image is `linux/amd64`: on arm64 it runs emulated, which is slow,
and needs binfmt to build at all.

Name configurations to run a subset (`... gl-repro verify+forbid no_verify+prefer`), or set `MODULES`
to a comma-separated list of modules. Interrupting is safe — re-running resumes.

## Output

`out/<config>.jsonl`, one object per module **attempt**:

```json
{"module": "…", "ok": true, "outcome": "ok", "injected_line": 19, "messages": [], "decls": [ … ]}
```

`outcome` ∈ {`ok`, `error`, `timeout`, `killed`}. **Only `ok` and `error` are verdicts**; the other
two mean the run was cut short and re-running retries them — so a retried module appears more than
once, and its verdict is the last record whose `outcome` is `ok` or `error`. Aggregating naively over
lines double-counts. A `timeout` record carries the declarations elaborated before the deadline, not
none.

Each `decls` entry is what the linter recorded for one declaration: `heartbeats`, a per-declaration
`outcome` (`analyzed` / `untargeted` / `noGraph` / `aborted`), and any suggestion's binder index,
shape (`weaken` / `split` / `drop`), targets and grade. `messages` holds the diagnostics the module
emitted; `injected_line` is where the linter import was inserted.

**`analyzed` with no emissions does not mean "nothing to weaken".** When a heartbeat budget is
exhausted the linter returns no candidates and records exactly that shape, so budget-censored
declarations are indistinguishable from clean negatives. At the 20M budget roughly 4% of analysed
declarations pile up against the cap; treat `heartbeats` near the budget as censored.

`out/meta.json` records the options, grid, exclusions and provenance (toolchain, Mathlib revision,
linter revision), plus one `segments` entry per invocation.

## Resources

Each concurrent `lean` holds ~1 GiB, so `JOBS` defaults to `min(cores // 3, ceiling / 1.5 GiB)` from
the memory ceiling the container can observe — 5 on a 32-core, 8 GiB Docker Desktop VM, but 2 on an
8-core one. Do not raise it past what memory allows: an OOM-killed `lean` is recorded as `killed` and
retried, but over-subscription trades data for nothing. Give the container memory instead.

`THREADS` caps threads within each `lean` and is needed independently — one uncapped `lean` averages
~8 threads, and `LEAN_NUM_THREADS` is ignored, so the cap must be the `--threads` flag.

Image 15.5 GB (14.4 GiB) on disk. Six configurations over 8,257 modules is ~35 CPU-hours ÷ `JOBS`,
so on the order of a day and a half at `JOBS=5`, plus any timeout tail. `out/` reaches ~150 MB.

## Linter cost comparison

`LINTER_PERF=1` replaces the grid with four configurations that toggle linters (`hb+neither`,
`hb+mathlib`, `hb+ours`, `hb+both`) and records whole-module heartbeats as `module_heartbeats`. A
linter's cost is the difference between configurations; the run forces one thread, because
`IO.getNumHeartbeats` counts only the current thread. Two caveats when reading the numbers: check
`neither <= mathlib <= both` and `neither <= ours <= both` per module, since a violation means a
truncated reading; and roughly 4M heartbeats of every total is import loading, which cancels in
differences but must be subtracted before quoting a share of module elaboration.

## The grid

`verify` ∈ {false, true} × `splitPolicy` ∈ {forbid, allow, prefer}, subsumption and both guards at
their defaults, 20M heartbeat budgets. `verify+forbid` is the production configuration, `no_verify+prefer`
the most permissive.

**Every configuration runs the whole corpus.** Restricting the cheaper cells to the modules the
permissive one flagged would be ~4× faster but unsound: `split = prefer` does more generation work, so
it can exhaust `generationHeartbeats` and return nothing exactly where `split = forbid` succeeds
(measured on `Module.associatedPrimes.mem_..._of_isLocalizedModule`). Permissiveness is not a superset
once the budget is finite.

## Excluded modules

Seven modules cannot be swept. Mathlib compiles all seven; what fails is re-elaborating a *copy* of a
module against an environment that already holds the compiled original. Five are in the linter's
import cone, so injecting `import GeneralizationLinter` redeclares their constants — a real limit on
coverage, since any module the linter transitively imports is unsweepable. The other two load Penrose
assets by a source-relative path and fail with the linter absent too. `run.py` lists both groups.
