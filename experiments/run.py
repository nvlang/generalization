#!/usr/bin/env python3
"""Reproduce the `verify` x `splitPolicy` grid over Mathlib.

    OUT=/out [JOBS=n] [THREADS=n] [TIMEOUT=s] [MODULES=a,b] [LINTER_PERF=1] python3 run.py [CONFIG ...]

Every configuration runs over the whole corpus. Output: $OUT/<config>.jsonl, plus $OUT/meta.json.
"""
import datetime, json, os, pathlib, re, subprocess, sys
from concurrent.futures import ThreadPoolExecutor, as_completed

ROOT = pathlib.Path(__file__).resolve().parent
MATHLIB = ROOT / ".lake" / "packages" / "mathlib"
OUT = pathlib.Path(os.environ.get("OUT", "/out"))
THREADS = int(os.environ.get("THREADS", 2))
TIMEOUT = float(os.environ.get("TIMEOUT", 1800))
GIB_PER_JOB = 1.5  # measured: ~1 GiB resident per concurrent `lean`
_NO_LIMIT = 2**62  # cgroup v1 encodes "unlimited" as a number near 2^63


def memory_ceiling_gib():
    for path in ("/sys/fs/cgroup/memory.max", "/sys/fs/cgroup/memory/memory.limit_in_bytes"):
        try:
            raw = pathlib.Path(path).read_text().strip()
        except OSError:
            continue
        if raw != "max" and raw.isdigit() and int(raw) < _NO_LIMIT:
            return int(raw) / 2**30
    try:
        return os.sysconf("SC_PAGE_SIZE") * os.sysconf("SC_PHYS_PAGES") / 2**30
    except (ValueError, OSError):
        return 8.0


def default_jobs():
    # Memory-bound, not just core-bound: an OOM-killed `lean` emits no records, which is
    # indistinguishable from a module the linter cleared.
    return max(1, min((os.cpu_count() or 4) // 3, int(memory_ceiling_gib() / GIB_PER_JOB)))


JOBS = int(os.environ.get("JOBS") or default_jobs())

# Mathlib's own `mathlibLeanOptions` (its lakefile.lean), then the linter's. `lean` is invoked
# directly rather than through lake, so anything absent here is simply not set.
OPTIONS = {
    "pp.unicode.fun": "true",
    "autoImplicit": "false",
    "maxSynthPendingDepth": "3",
    "weak.linter.mathlibStandardSet": "true",
    "weak.linter.style.header": "true",
    "weak.linter.checkInitImports": "true",
    "weak.linter.allScriptsDocumented": "true",
    "weak.linter.pythonStyle": "true",
    "weak.linter.style.longFile": "1500",
    "weak.linter.generalizeTypeclasses": "true",
    "weak.generalizationLinter.stats": "true",
    "weak.generalizeTypeclasses.generationHeartbeats": "20000000",
    "weak.generalizeTypeclasses.perCandidateHeartbeats": "20000000",
}
GRID = {
    f"{'verify' if v else 'no_verify'}+{s}": {
        "weak.generalizeTypeclasses.verify": "true" if v else "false",
        "weak.generalizeTypeclasses.split": s,
    }
    for v in (0, 1)
    for s in ("forbid", "allow", "prefer")
}

# LINTER_PERF=1 measures whole-module heartbeats with linters toggled, instead of sweeping. Costs are
# read off as differences; `Elab.async=false` is required because the counter is per-thread.
PROBE = 'run_cmd Lean.logInfo s!"GL_HB {← IO.getNumHeartbeats}"'
PERF = os.environ.get("LINTER_PERF", "") not in ("", "0", "false")  # bool("0") is True
_ML_OFF = {
    "weak.linter.mathlibStandardSet": "false",
    "weak.linter.style.header": "false",
    "weak.linter.checkInitImports": "false",
    "weak.linter.allScriptsDocumented": "false",
    "weak.linter.pythonStyle": "false",
}
_GL_OFF = {"weak.linter.generalizeTypeclasses": "false"}
PERF_GRID = {
    "hb+neither": {"Elab.async": "false", **_ML_OFF, **_GL_OFF},
    "hb+mathlib": {"Elab.async": "false", **_GL_OFF},
    "hb+ours": {"Elab.async": "false", **_ML_OFF},
    "hb+both": {"Elab.async": "false"},
}

# Mathlib compiles all seven; it is this shadow method that cannot.
EXCLUDED = {
    # In the linter's import cone: the shadow's `import GeneralizationLinter` pulls these back in as
    # compiled imports, so re-elaborating them redeclares their constants.
    "Mathlib/Lean/Elab/InfoTree.lean",
    "Mathlib/Lean/Environment.lean",
    "Mathlib/Tactic/Linter/Header.lean",
    "Mathlib/Tactic/Linter/DirectoryDependency.lean",
    "Mathlib/Lean/Expr/Basic.lean",
    # Load Penrose assets by a source-relative path, which the shadow's location breaks. These fail
    # with the linter absent too.
    "Mathlib/Tactic/Widget/CommDiag.lean",
    "Mathlib/Tactic/Widget/StringDiagram.lean",
}
IMPORT = re.compile(r"^\s*(public\s+)?(meta\s+)?import\b")  # `public meta import` occurs


def module_of(rel):
    return rel[: -len(".lean")].replace("/", ".")


def provenance():
    rev = None
    try:
        manifest = json.loads((ROOT / "lake-manifest.json").read_text())
        rev = next(
            (p.get("rev") for p in manifest.get("packages", []) if p.get("name") == "mathlib"), None
        )
    except (OSError, json.JSONDecodeError):
        pass
    try:
        toolchain = (ROOT / "lean-toolchain").read_text().strip()
    except OSError:
        toolchain = None
    return {
        "toolchain": toolchain,
        "mathlib_rev": rev,
        "linter_revision": os.environ.get("GL_REVISION"),
    }


def inject(src):
    """Import the linter in the file's header. Module-system files need `meta import`, or the linter
    never fires; import-lookalikes inside docstrings must not attract the insertion."""
    lines, is_module, at, depth = src.split("\n"), False, 0, 0
    for i, line in enumerate(lines):
        if depth:
            depth += line.count("/-") - line.count("-/")
            continue
        code = line.split("--", 1)[0].strip()
        if IMPORT.match(code) or code == "module":
            is_module = is_module or code == "module"
            at = i + 1
        elif code and not code.startswith("/-"):
            break
        depth += code.count("/-") - code.count("-/")
    lines.insert(at, ("meta " if is_module else "") + "import GeneralizationLinter")
    return "\n".join(lines), is_module, at + 1


def elaborate(rel, flags, env, tmp):
    module = module_of(rel)
    src, is_module, injected_line = inject((MATHLIB / rel).read_text())
    if PERF:
        src += "\n" + PROBE + "\n"
    stem = f"{module}.{os.getpid()}"  # PID-qualified: two sweeps may share one OUT
    lean_file, setup = tmp / f"{stem}.lean", tmp / f"{stem}.json"
    lean_file.write_text(src)
    setup.write_text(
        json.dumps(
            {
                "name": module,
                "isModule": is_module,
                "importArts": {},
                "dynlibs": [],
                "plugins": [],
                "options": {},
            }
        )
    )
    # PERF forces one thread. `IO.getNumHeartbeats` counts the CURRENT THREAD, and `Elab.async=false`
    # alone does not pin the module to one: the header task and the command tasks can land on
    # different pool threads, and the probe then reports only its own. Measured at --threads=2: ~3% of
    # runs short by 7-44%, one attributing a NEGATIVE cost. 130/130 identical at --threads=1.
    threads = 1 if PERF else THREADS
    argv = ["lean", "--json", "--setup", str(setup), f"--threads={threads}", *flags, str(lean_file)]
    try:
        proc = subprocess.run(
            argv, cwd=ROOT, env=env, capture_output=True, text=True, timeout=TIMEOUT
        )
        stdout, rc = proc.stdout, proc.returncode
    except subprocess.TimeoutExpired as e:
        raw = e.stdout or ""  # bytes even under text=True
        stdout = raw.decode(errors="replace") if isinstance(raw, bytes) else raw
        rc = None
    finally:
        lean_file.unlink(missing_ok=True)
        setup.unlink(missing_ok=True)
    decls, messages, module_hb = [], [], None
    for line in stdout.splitlines():
        if not line.startswith("{"):
            continue
        try:
            msg = json.loads(line)
        except json.JSONDecodeError:
            continue
        data = msg.get("data", "")
        # Locate the marker in the DECODED field; an offset taken from the raw line never parses.
        i = data.find("GL_STATS ")
        if i >= 0:
            st = json.loads(data[i + len("GL_STATS ") :])
            st.pop(
                "graph", None
            )  # absent in this revision; dropped for parity with the local harness
            decls.append(st)
        elif data.startswith("GL_HB "):
            module_hb = int(data.split()[1])
        else:
            # Kept because the analysis pipeline reads the emitted diagnostics, not just `decls`.
            messages.append(
                {k: msg.get(k) for k in ("kind", "severity", "data")}
                | {"line": (msg.get("pos") or {}).get("line")}
            )
    # Negative rc is a signal (usually the OOM killer), None is the timeout. Neither is a verdict.
    outcome = "ok" if rc == 0 else "timeout" if rc is None else "killed" if rc < 0 else "error"
    rec = {
        "module": module,
        "ok": rc == 0,
        "outcome": outcome,
        "injected_line": injected_line,
        "messages": messages,
        "decls": decls,
    }
    if PERF:
        rec["module_heartbeats"] = module_hb
    return rec


def main():
    mem = memory_ceiling_gib()
    print(
        f"jobs={JOBS} threads={THREADS}  ({os.cpu_count()} cpus, {mem:.1f} GiB ceiling, "
        f"budgeting {GIB_PER_JOB} GiB/job)",
        flush=True,
    )
    if JOBS * GIB_PER_JOB > mem:
        print(
            f"  WARNING: JOBS={JOBS} wants ~{JOBS * GIB_PER_JOB:.0f} GiB of {mem:.1f} GiB. "
            f"OOM-killed elaborations look like clean modules.",
            flush=True,
        )
    # check=True, and the LEAN_PATH guard: an empty search path would yield a complete-looking
    # all-zero dataset rather than an error.
    env = dict(os.environ)
    lake_env = subprocess.run(
        ["lake", "env"], cwd=ROOT, capture_output=True, text=True, check=True
    ).stdout
    for line in lake_env.splitlines():
        key, sep, val = line.partition("=")
        if sep:
            env[key] = val
    if not env.get("LEAN_PATH"):
        sys.exit("`lake env` reported no LEAN_PATH; refusing to sweep")
    # Both halves matter: globbing the package would add Archive/ and MathlibTest/ to the corpus, and
    # a `mathlib/`-prefixed path matches no EXCLUDED entry.
    files = sorted(str(p.relative_to(MATHLIB)) for p in (MATHLIB / "Mathlib").rglob("*.lean"))
    files = [f for f in files if f not in EXCLUDED]
    if os.environ.get("MODULES"):
        want = {m.strip() for m in os.environ["MODULES"].split(",") if m.strip()}
        files = [f for f in files if module_of(f) in want]
        unknown = want - {module_of(f) for f in files}
        if unknown:  # fatal, not ignored: a typo would silently shrink the run
            sys.exit(f"MODULES names {len(unknown)} module(s) not in the corpus: {sorted(unknown)}")
    OUT.mkdir(parents=True, exist_ok=True)
    tmp = OUT / "tmp"
    tmp.mkdir(exist_ok=True)
    grid = PERF_GRID if PERF else GRID
    if [n for n in sys.argv[1:] if n not in grid]:
        sys.exit(
            f"unknown config(s) {[n for n in sys.argv[1:] if n not in grid]}; have {sorted(grid)}"
        )
    # Appended, not overwritten: a resumed run would otherwise leave a meta.json describing only its
    # last segment, so nothing would record what the dataset as a whole was produced by.
    meta_path = OUT / "meta.json"
    try:
        meta = json.loads(meta_path.read_text())
    except (OSError, json.JSONDecodeError):
        meta = {}
    meta.setdefault("segments", []).append(
        {
            "started": datetime.datetime.now(datetime.timezone.utc).isoformat(timespec="seconds"),
            "modules": len(files),
            "jobs": JOBS,
            "threads": THREADS,
            "timeout_s": TIMEOUT,
            "memory_ceiling_gib": round(memory_ceiling_gib(), 2),
            "configs_requested": sorted(sys.argv[1:] or grid),
        }
    )
    meta |= {
        "options": OPTIONS,
        "grid": grid,
        "excluded": sorted(EXCLUDED),
        "provenance": provenance(),
    }
    meta_path.write_text(json.dumps(meta, indent=2))
    for name in sys.argv[1:] or grid:
        flags = [f"-D{k}={v}" for k, v in {**OPTIONS, **grid[name]}.items()]
        done = OUT / f"{name}.jsonl"
        # Only `ok`/`error` count as done, so timeouts and kills are retried; a truncated final line
        # from an interrupted run is skipped rather than fatal.
        seen = set()
        if done.exists():
            for line in done.read_text().splitlines():
                try:
                    rec = json.loads(line)
                except json.JSONDecodeError:
                    continue
                if rec.get("outcome", "ok" if rec.get("ok") else "error") in ("ok", "error"):
                    seen.add(rec.get("module"))
        todo = [f for f in files if module_of(f) not in seen]
        print(f"[{name}] {len(todo)} modules to do ({len(seen)} already recorded)", flush=True)
        # A run killed mid-write leaves a fragment with no trailing newline. Appending after it would
        # fuse the next record onto the fragment, making BOTH unparseable -- so that module would
        # vanish from the dataset while the run still reported success. Terminate the fragment first.
        if done.exists() and done.stat().st_size and not done.read_bytes().endswith(b"\n"):
            with done.open("a") as f:
                f.write("\n")
        tally = {}
        with done.open("a") as out, ThreadPoolExecutor(JOBS) as pool:
            futures = [pool.submit(elaborate, f, flags, env, tmp) for f in todo]
            try:
                # as_completed, not map: map would block finished results behind one slow module.
                for n, fut in enumerate(as_completed(futures), 1):
                    rec = fut.result()
                    tally[rec["outcome"]] = tally.get(rec["outcome"], 0) + 1
                    out.write(json.dumps(rec) + "\n")
                    out.flush()
                    if n % 200 == 0:
                        print(f"[{name}] {n}/{len(todo)} {tally}", flush=True)
            finally:
                # Without this, Ctrl-C leaves the executor draining every queued module with nobody
                # left to write the results -- hours of elaboration discarded after the interrupt.
                pool.shutdown(cancel_futures=True)
        print(f"[{name}] complete: {tally}", flush=True)
        if tally.get("timeout") or tally.get("killed"):
            print(
                f"[{name}] WARNING: {tally.get('timeout', 0)} timed out, "
                f"{tally.get('killed', 0)} killed; partial records, not verdicts. Re-run to retry.",
                flush=True,
            )


if __name__ == "__main__":
    main()
