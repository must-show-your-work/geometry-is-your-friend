# Rebuild the theorem graph database from a clean Lean build.
# Requires `nix develop` so `kuzu` (CLI + Python) and venv are on PATH.
#
# The dumptactics pass is the heavy one — every `Geometry/**.lean` is
# re-elaborated with a full Mathlib import. We dispatch that via
# `scripts/run_dumptactics.py`, which spawns one subprocess per module
# (so RAM is fully released between modules) with per-subprocess
# `nice`/`ionice` and a `ulimit -v` cap so a runaway elaboration gets
# killed by the kernel before it can hang the machine. Per-module
# mtime cache means second runs only re-do touched files.
graph:
    #!/usr/bin/env bash
    # Shebang recipe so subshell-level `exec > >(tee …)` redirection
    # carries across every command instead of being reset between
    # lines (just's default is one shell per recipe line).
    set -euo pipefail
    rm -f blueprint/obvious_uses.jsonl
    # Tee the whole pipeline (stdout + stderr) into blueprint/graph.log
    # so panic traces / build errors are still around to `grep` after
    # the fact. Each run overwrites the previous log; copy aside
    # beforehand if you need history.
    exec > >(tee blueprint/graph.log) 2>&1
    # Force a clean rebuild with `GIYF_DUMP_DEPS=1` so every `obvious`
    # invocation appends its `(module, line, stage, closer)` record to
    # blueprint/obvious_uses.jsonl. Lake's `.olean` cache wouldn't
    # re-run tactic elaboration without the clean. Env var rather than
    # a Lean option because custom options can't be set via Lake's `-D`.
    lake clean
    GIYF_DUMP_DEPS=1 lake build
    # Use `lean --run` rather than `lake exe` — the latter native-compiles
    # via clang and on NixOS hits a missing `-lc++` / `-lgmp` / `-luv`
    # cascade unless the dev shell exports `LIBRARY_PATH` correctly.
    lake env lean --run scripts/DumpDecls.lean
    lake env lean --run scripts/DumpImports.lean
    lake env lean --run scripts/DumpFigures.lean
    python scripts/run_dumptactics.py || true
    python scripts/ingest.py
    python scripts/export_graph.py

# Fast iteration on the obvious-uses pipeline only — skips
# `run_dumptactics.py` (the slow per-module re-elaboration) so the
# rebuild + re-ingest path runs in a couple of minutes instead of 20+.
# Highlighted source in the viewer stays stale; everything else
# (deletions, new tags, obvious_uses chips) is fresh. Use `just graph`
# for a full refresh.
dump-obvious:
    rm -f blueprint/obvious_uses.jsonl
    lake clean
    GIYF_DUMP_DEPS=1 lake build
    lake env lean --run scripts/DumpDecls.lean
    lake env lean --run scripts/DumpImports.lean
    lake env lean --run scripts/DumpFigures.lean
    python scripts/ingest.py
    python scripts/export_graph.py

# Serve the static dep-graph viewer over HTTP (browsers block `file://`
# `fetch` of sibling JSON, so a local server is the path of least resistance).
# Assumes `just graph` has produced blueprint/graph.json.
graph-view port="8765":
    @echo "Open http://localhost:{{port}}/scripts/graph.html"
    @python -m http.server {{port}}

# Serve the table-of-contents viewer (parallel to `graph-view`). Same
# data source; left pane lists every atlas decl grouped by kind/file,
# right pane renders the selected decl's card. The card layout here is
# the source of truth that the graph view will eventually adopt.
toc-view port="8765":
    @echo "Open http://localhost:{{port}}/scripts/toc.html"
    @python -m http.server {{port}}

# Run a bundled query, or list them when called with no name.
#   `just q`              — list all queries with one-line descriptions
#   `just q sorry_blocked`— print the query's legend, then run it
q name="":
    @./scripts/q.sh "{{name}}"
