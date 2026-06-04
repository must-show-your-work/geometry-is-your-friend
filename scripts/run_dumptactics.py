#!/usr/bin/env python3
"""Orchestrator for `lake exe dumptactics`.

Discovers every `Geometry/**.lean` and runs `lake exe dumptactics
MOD` as a fresh subprocess per module. Each invocation imports
Mathlib from scratch, processes its single module, writes its cache
file, and exits — so RAM is fully released between modules instead of
accumulating.

Each subprocess runs at the lowest CPU + I/O priority and is capped
by `ulimit -v` so a runaway elaboration (Mathlib unifier exploding,
etc.) gets killed by the kernel before it can hang the system. The
per-subprocess cap is conservative-but-generous so legitimate heavy
modules still complete.

After all subprocesses run (or fail individually), the per-module
cache files in `blueprint/highlighted-cache/` are concatenated into
the two master files that `export_graph.py` consumes:

  - blueprint/highlighted.json — { decl_name: html_string }
  - blueprint/tactics.json     — [{ decl, tactic, line }, …]

Modules with an up-to-date cache are skipped at the Python layer (no
subprocess started) so re-running after a touched-source edit only
spends time on the actually-changed files.
"""
from __future__ import annotations
import re
import shutil
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
GEO_DIR = ROOT / "Geometry"
CACHE_DIR = ROOT / "blueprint" / "highlighted-cache"
BP_DIR = ROOT / "blueprint"

# Path to a shell that understands `ulimit` (a POSIX shell builtin).
# `subprocess.run(executable=…)` defaults to `/bin/sh` which doesn't
# exist on NixOS in the usual place, so resolve via PATH instead.
SHELL = shutil.which("bash") or shutil.which("sh")
if SHELL is None:
    sys.exit("run_dumptactics: no bash/sh on PATH")

ULIMIT_V_KB = 12_000_000


# Top-level keywords that introduce something `DumpTactics` might
# actually want to extract. Files with none of these are umbrella
# files (just `import …` lines + `namespace`/`open`/`end`) and have
# no decls to dump — running them through SubVerso's frontend
# re-elab burns the entire import closure for zero output, and on
# heavy umbrellas (Ch2.Prop, Ch3.Prop) consistently blows past the
# vmem cap with "failed to create thread".
_DECL_KW = re.compile(
    r"^\s*"
    r"(?:@\[[^\]]+\]\s*)*"            # optional attribute(s)
    r"(?:public\s+|private\s+|protected\s+|noncomputable\s+|unsafe\s+|partial\s+)*"
    r"(?:def|theorem|lemma|example|axiom|structure|inductive|"
    r"class|instance|abbrev|opaque|atlas\s+\S+)\b",
    re.MULTILINE,
)


def has_decls(path: Path) -> bool:
    """Cheap scan for any decl keyword. Misses macros / syntax / elab
    declarations but those don't carry tactic content anyway. False
    means "skip — pure umbrella"."""
    try:
        text = path.read_text(encoding="utf-8", errors="replace")
    except OSError:
        return True  # fail-open: if we can't read it, let DumpTactics try
    return bool(_DECL_KW.search(text))


def discover_modules() -> list[str]:
    """Return dotted module names for every `Geometry/**.lean` file
    that carries at least one decl. Pure-umbrella files (just
    `import …` chains) are skipped — see `has_decls`."""
    out: list[str] = []
    skipped: list[str] = []
    for p in GEO_DIR.rglob("*.lean"):
        rel = p.relative_to(ROOT)
        dotted = str(rel.with_suffix("")).replace("/", ".")
        if has_decls(p):
            out.append(dotted)
        else:
            skipped.append(dotted)
    if skipped:
        print(f"[run_dumptactics] skipping {len(skipped)} umbrella "
              f"module(s) with no decls: {', '.join(skipped[:6])}"
              f"{' …' if len(skipped) > 6 else ''}",
              flush=True)
    return sorted(out)


def cache_file(mod: str) -> Path:
    return CACHE_DIR / f"{mod}.cache"


def src_file(mod: str) -> Path:
    return ROOT / (mod.replace(".", "/") + ".lean")


def cache_up_to_date(mod: str) -> bool:
    """True if the per-module cache is strictly newer than the source.
    Mirrors `DumpTactics.lean`'s `cacheUpToDate` so the Python layer
    can short-circuit before paying subprocess-startup cost."""
    cf = cache_file(mod)
    if not cf.exists():
        return False
    sf = src_file(mod)
    if not sf.exists():
        # Source disappeared but cache stayed; trust the cache.
        return True
    return cf.stat().st_mtime > sf.stat().st_mtime


def run_one(mod: str, idx: int, total: int) -> int:
    """Spawn `lake exe dumptactics MOD` in a niced/ulimited subprocess.
    Returns the exit code (non-zero ≠ fatal here; we just log and move
    on so one bad module doesn't block the rest)."""
    # `MALLOC_ARENA_MAX=2` caps glibc's per-thread malloc arenas (each
    # ~64 MB of vmem) to two total. Lean+SubVerso spawn many threads
    # internally; without this each arena counts against the per-
    # subprocess vmem cap and `mmap` for new thread stacks starts
    # failing with `lean::exception: failed to create thread`. Also
    # shrink the thread stack from glibc's default 8 MB to 2 MB so
    # each thread costs less vmem; Lean's elaborator isn't deeply
    # recursive in our codebase.
    cmd = (
        f"ulimit -v {ULIMIT_V_KB} && "
        f"ulimit -s 2048 && "
        f"nice -n 19 ionice -c 3 "
        f"env LEAN_NUM_THREADS=1 MALLOC_ARENA_MAX=2 "
        f"lake env lean --run scripts/DumpTactics.lean {mod}"
    )
    print(f"[run_dumptactics] [{idx}/{total}] {mod}", flush=True)
    r = subprocess.run(cmd, shell=True, executable=SHELL, cwd=ROOT)
    if r.returncode != 0:
        print(
            f"[run_dumptactics] [{idx}/{total}] {mod} → exit {r.returncode} "
            f"(continuing; partial cache, if any, preserved)",
            flush=True,
        )
    return r.returncode


def parse_cache(path: Path) -> tuple[list[str], list[str]]:
    """Read a per-module cache file and return its (html_entries,
    tactic_entries) lists. Entries are pre-formatted JSON fragments
    ready to drop into the master arrays."""
    html: list[str] = []
    tactics: list[str] = []
    sect: str | None = None
    version_ok = False
    saw_version = False
    for line in path.read_text().splitlines():
        if line == "__VERSION__":
            sect = "version"
        elif line == "__HTML__":
            sect = "html"
        elif line == "__TACTICS__":
            sect = "tactics"
        elif sect == "version" and not saw_version:
            saw_version = True
            version_ok = (line.strip() == "v1")
        elif sect == "html" and line.startswith("  "):
            if version_ok:
                html.append(line)
        elif sect == "tactics" and line.startswith("  "):
            if version_ok:
                tactics.append(line)
    return html, tactics


def assemble_master() -> None:
    BP_DIR.mkdir(parents=True, exist_ok=True)
    CACHE_DIR.mkdir(parents=True, exist_ok=True)
    html_all: list[str] = []
    tactics_all: list[str] = []
    for cf in sorted(CACHE_DIR.glob("*.cache")):
        h, t = parse_cache(cf)
        html_all.extend(h)
        tactics_all.extend(t)
    html_master = "{\n" + ",\n".join(html_all) + "\n}\n"
    tactics_master = "[\n" + ",\n".join(tactics_all) + "\n]\n"
    (BP_DIR / "highlighted.json").write_text(html_master)
    (BP_DIR / "tactics.json").write_text(tactics_master)
    print(
        f"[run_dumptactics] assembled master: "
        f"{len(html_all)} decls, {len(tactics_all)} tactic occurrences",
        flush=True,
    )


def main() -> int:
    mods = discover_modules()
    print(f"[run_dumptactics] discovered {len(mods)} modules", flush=True)
    skipped = 0
    failed = 0
    for i, mod in enumerate(mods, 1):
        if cache_up_to_date(mod):
            skipped += 1
            print(f"[run_dumptactics] [{i}/{len(mods)}] {mod} (cached)",
                  flush=True)
            continue
        rc = run_one(mod, i, len(mods))
        if rc != 0:
            failed += 1
    print(f"[run_dumptactics] done: "
          f"{skipped} cached, {len(mods) - skipped - failed} processed, "
          f"{failed} failed", flush=True)
    assemble_master()
    return 0


if __name__ == "__main__":
    sys.exit(main())
