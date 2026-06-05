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
    # Per-step bracket markers — make it easy to see in graph.log
    # exactly which stage was reached. An earlier run silently stopped
    # after `lake build` and the log gave no indication where; these
    # echos guarantee a breadcrumb on either side of every command.
    step() { echo; echo "[graph] >>> $* @ $(date '+%H:%M:%S')"; }
    step "lake update subverso"
    lake update subverso
    step "lake clean"
    lake clean
    step "GIYF_DUMP_DEPS=1 lake build (default target = Geometry)"
    GIYF_DUMP_DEPS=1 lake build
    step "lake build subverso (forced — Geometry doesn't transitively pull it)"
    lake build subverso
    step "DumpDecls"
    lake env lean --run scripts/DumpDecls.lean
    step "DumpImports"
    lake env lean --run scripts/DumpImports.lean
    step "DumpFigures"
    lake env lean --run scripts/DumpFigures.lean
    step "DumpAuxFigures"
    lake env lean --run scripts/DumpAuxFigures.lean
    step "DumpTypeTeX"
    lake env lean --run scripts/DumpTypeTeX.lean
    step "run_dumptactics.py"
    python scripts/run_dumptactics.py || true
    step "ingest.py"
    python scripts/ingest.py
    step "export_graph.py"
    python scripts/export_graph.py
    step "done"

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
    # SubVerso isn't transitively imported by `Geometry`, only by
    # `scripts/DumpTactics.lean`. Default-target build skips it, so
    # build it explicitly here — otherwise the dumptactics script
    # bails with "unknown module prefix 'SubVerso'".
    lake build subverso
    lake env lean --run scripts/DumpDecls.lean
    lake env lean --run scripts/DumpImports.lean
    lake env lean --run scripts/DumpFigures.lean
    lake env lean --run scripts/DumpAuxFigures.lean
    lake env lean --run scripts/DumpTypeTeX.lean
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
#   `just q module_deps_of Geometry.Ch3.Prop.P5` — extra args are spliced
#                          into the cypher body as $1/$2/… replacements,
#                          for parameterized queries.
q name="" *args="":
    @./scripts/q.sh "{{name}}" {{args}}
