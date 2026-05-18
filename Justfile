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
    lake build
    lake exe dumpdecls
    lake exe dumpimports
    -python scripts/run_dumptactics.py
    python scripts/ingest.py
    python scripts/export_graph.py

# Serve the static dep-graph viewer over HTTP (browsers block `file://`
# `fetch` of sibling JSON, so a local server is the path of least resistance).
# Assumes `just graph` has produced blueprint/graph.json.
graph-view port="8765":
    @echo "Open http://localhost:{{port}}/scripts/graph.html"
    @python -m http.server {{port}}

# Run a bundled query, or list them when called with no name.
#   `just q`              — list all queries with one-line descriptions
#   `just q sorry_blocked`— print the query's legend, then run it
q name="":
    @./scripts/q.sh "{{name}}"
