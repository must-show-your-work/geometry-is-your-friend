#!/usr/bin/env bash
# Wrapper around the Kuzu DB:
#   `q` (no args)            — list every query with its one-line description
#   `q <name>`               — print the query's legend, then run it
#   `q <name> <arg1> [arg2…]` — same, with $1/$2/… substituted in the
#                              query body before execution
#
# Runs the query via the kuzu Python driver in the project venv. The `kuzu`
# CLI binary (in the Nix dev shell) would also work, but the Python path
# avoids a PATH-dependency.
set -euo pipefail

QUERIES_DIR="scripts/queries"
DB_PATH="blueprint/graph.kuzu"

if [ "$#" -eq 0 ] || [ -z "${1:-}" ]; then
  printf "Available queries (run with \`just q <name>\`):\n\n"
  for f in "$QUERIES_DIR"/*.cypher; do
    name=$(basename "$f" .cypher)
    desc=$(awk '/^[[:space:]]*\/\//{
      sub(/^[[:space:]]*\/\/[[:space:]]?/, "");
      print; exit
    }' "$f")
    printf "  %-22s  %s\n" "$name" "$desc"
  done
  exit 0
fi

name="$1"
file="$QUERIES_DIR/$name.cypher"
if [ ! -f "$file" ]; then
  printf "no such query: %s\n" "$name" >&2
  printf "run \`just q\` (no args) to list available queries\n" >&2
  exit 1
fi

# Print the leading `//` comment block as a legend.
printf -- "--- %s ---\n" "$name"
awk '/^[[:space:]]*\/\//{
  sub(/^[[:space:]]*\/\/[[:space:]]?/, "");
  print "  " $0; next
} {exit}' "$file"
printf "\n"

# Argument substitution: any extra args after the query name are spliced
# into the cypher body as $1/$2/… literal replacements. Used by
# parameterized queries like `module_deps_of $1`. No substitution happens
# when no extra args are passed, so non-parameterized queries are unaffected.
shift
if [ "$#" -gt 0 ]; then
  rendered=$(mktemp /tmp/q-XXXXXX.cypher)
  trap 'rm -f "$rendered"' EXIT
  cp "$file" "$rendered"
  i=1
  for a in "$@"; do
    # Quote sed delimiters in the argument so module names with '.' work.
    esc=$(printf '%s' "$a" | sed 's/[\/&]/\\&/g')
    sed -i "s/\$${i}\b/${esc}/g" "$rendered"
    i=$((i + 1))
  done
  file="$rendered"
fi

exec .venv/bin/python scripts/run_query.py "$file" "$DB_PATH"
