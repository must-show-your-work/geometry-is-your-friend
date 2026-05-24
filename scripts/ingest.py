#!/usr/bin/env python3
"""
Ingest the theorem-graph JSON dumps into a Kuzu database.

Reads:
  blueprint/decls.json     — produced by `lake exe dumpdecls`
  blueprint/modules.json   — produced by `lake exe dumpimports`
  blueprint/tactics.json   — produced by `lake exe dumptactics` (optional)

Writes:
  blueprint/graph.kuzu/    — Kuzu database directory

Re-runnable: drops & recreates the database each time. The schema lives in
scripts/schema.cypher so it can be tweaked without touching this script.
"""

from __future__ import annotations

import json
import shutil
from pathlib import Path

import kuzu


PROJECT_ROOT = Path(__file__).resolve().parent.parent
BLUEPRINT_DIR = PROJECT_ROOT / "blueprint"
DB_PATH = BLUEPRINT_DIR / "graph.kuzu"
SCHEMA_PATH = PROJECT_ROOT / "scripts" / "schema.cypher"


def load_json(path: Path):
    if not path.exists():
        return None
    return json.loads(path.read_text())


def run_schema(conn: kuzu.Connection) -> None:
    """Execute each statement in schema.cypher. Statements separated by ';' on
    their own line; lines starting with '//' are treated as comments."""
    raw = SCHEMA_PATH.read_text()
    # Strip line comments before splitting on ';'.
    cleaned_lines = []
    for line in raw.splitlines():
        stripped = line.strip()
        if stripped.startswith("//"):
            continue
        cleaned_lines.append(line)
    body = "\n".join(cleaned_lines)
    for stmt in body.split(";"):
        stmt = stmt.strip()
        if stmt:
            conn.execute(stmt)


def insert_decls(conn: kuzu.Connection, decls: list[dict]) -> int:
    for d in decls:
        # Coerce nullable line numbers.
        line_start = d.get("line_start")
        line_end = d.get("line_end")
        conn.execute(
            """
            CREATE (:Decl {
              name: $name, kind: $kind, type_raw: $type_raw, type_pp: $type_pp,
              doc: $doc, namespace: $namespace, file: $file,
              line_start: $line_start, line_end: $line_end,
              has_sorry: $has_sorry, is_proposition: $is_proposition,
              is_noncomputable: $is_noncomputable,
              atlas_kind: $atlas_kind, atlas_number: $atlas_number,
              atlas_title: $atlas_title
            })
            """,
            {
                "name": d["name"],
                "kind": d["kind"],
                "type_raw": d.get("type", ""),
                "type_pp": d.get("type_pp", ""),
                "doc": d.get("doc", ""),
                "namespace": d.get("namespace", ""),
                "file": d.get("file", ""),
                "line_start": line_start if line_start is not None else -1,
                "line_end": line_end if line_end is not None else -1,
                "has_sorry": d.get("has_sorry", False),
                "is_proposition": d.get("is_proposition", False),
                "is_noncomputable": d.get("is_noncomputable", False),
                # Atlas attribute metadata. JSON `null` from the dumper
                # (decl had no `@[atlas …]`) maps cleanly to Kuzu NULL.
                "atlas_kind": d.get("atlas_kind"),
                "atlas_number": d.get("atlas_number"),
                "atlas_title": d.get("atlas_title"),
            },
        )
    return len(decls)


def insert_modules(conn: kuzu.Connection, mods: list[dict]) -> int:
    for m in mods:
        conn.execute(
            "CREATE (:Module {name: $name, file: $file})",
            {"name": m["name"], "file": m.get("file", "")},
        )
    return len(mods)


def insert_uses_edges(conn: kuzu.Connection, decls: list[dict]) -> int:
    """USES edges: skip dst names not present as a Decl node (these are
    `_proof_N` / `_simp_N` auxiliaries pruned by the dumper's denylist)."""
    decl_names = {d["name"] for d in decls}
    n = 0
    for d in decls:
        src = d["name"]
        for dst in d.get("deps", []):
            if dst not in decl_names or dst == src:
                continue
            conn.execute(
                """
                MATCH (a:Decl {name: $src}), (b:Decl {name: $dst})
                CREATE (a)-[:USES]->(b)
                """,
                {"src": src, "dst": dst},
            )
            n += 1
    return n


def insert_declared_in(
    conn: kuzu.Connection, decls: list[dict], mods: list[dict]
) -> int:
    mod_names = {m["name"] for m in mods}
    n = 0
    for d in decls:
        mod = d.get("module", "")
        if mod and mod in mod_names:
            conn.execute(
                """
                MATCH (a:Decl {name: $decl}), (m:Module {name: $mod})
                CREATE (a)-[:DECLARED_IN]->(m)
                """,
                {"decl": d["name"], "mod": mod},
            )
            n += 1
    return n


def insert_imports_edges(conn: kuzu.Connection, mods: list[dict]) -> int:
    mod_names = {m["name"] for m in mods}
    n = 0
    for m in mods:
        src = m["name"]
        for dst in m.get("imports", []):
            if dst in mod_names:
                conn.execute(
                    """
                    MATCH (a:Module {name: $src}), (b:Module {name: $dst})
                    CREATE (a)-[:IMPORTS]->(b)
                    """,
                    {"src": src, "dst": dst},
                )
                n += 1
    return n


def insert_obvious_uses(
    conn: kuzu.Connection,
    decls: list[dict],
    records: list[dict],
) -> tuple[int, int, int]:
    """Insert ObviousStage nodes (deduplicated) and OBVIOUS_USES edges.
    Each record (`{module, line, stage, closer}`) is joined to its
    enclosing decl by module match + line ∈ [line_start, line_end].
    Multiple records mapping to the same (decl, stage, closer) triple
    are aggregated into a single edge with `count` summed.

    Returns (n_stage_nodes, n_edges, n_orphan_records). Orphans are
    records whose `(module, line)` didn't match any decl's range —
    usually a sign of stale dump data."""
    from collections import defaultdict

    # Index decls by module for O(records · max_decls_per_module) match.
    by_mod: dict[str, list[dict]] = defaultdict(list)
    for d in decls:
        if d.get("module"):
            by_mod[d["module"]].append(d)

    def find_decl(module: str, line: int) -> dict | None:
        for d in by_mod.get(module, []):
            ls = d.get("line_start")
            le = d.get("line_end")
            if ls is not None and le is not None and ls <= line <= le:
                return d
        return None

    edges: dict[tuple[str, str, str], int] = defaultdict(int)
    stages: set[str] = set()
    orphans = 0
    for rec in records:
        d = find_decl(rec["module"], rec["line"])
        if d is None:
            orphans += 1
            continue
        key = (d["name"], rec["stage"], rec["closer"])
        edges[key] += 1
        stages.add(rec["stage"])

    for s in stages:
        conn.execute("CREATE (:ObviousStage {name: $n})", {"n": s})

    for (decl, stage, closer), count in edges.items():
        conn.execute(
            """
            MATCH (d:Decl {name: $decl}), (s:ObviousStage {name: $stage})
            CREATE (d)-[:OBVIOUS_USES {closer: $closer, count: $count}]->(s)
            """,
            {"decl": decl, "stage": stage, "closer": closer, "count": count},
        )

    return (len(stages), len(edges), orphans)


def load_jsonl(path: Path) -> list[dict]:
    """Read newline-delimited JSON. Returns [] if the file is missing."""
    if not path.exists():
        return []
    out: list[dict] = []
    for line in path.read_text().splitlines():
        line = line.strip()
        if not line:
            continue
        try:
            out.append(json.loads(line))
        except json.JSONDecodeError:
            continue  # tolerate truncated final lines / interleaving issues
    return out


def insert_tactics(conn: kuzu.Connection, tac_entries: list[dict]) -> tuple[int, int, int]:
    """Insert Tactic nodes (deduplicated) and USED_TACTIC edges. Returns
    (n_tactic_nodes, n_edges, n_decls_with_tactics)."""
    seen: set[str] = set()
    n_edges = 0
    for entry in tac_entries:
        for t in entry.get("tactics", []):
            seen.add(t["name"])
    for tac in seen:
        conn.execute("CREATE (:Tactic {name: $n})", {"n": tac})
    for entry in tac_entries:
        decl = entry["decl"]
        # Aggregate by tactic name; keep earliest line.
        agg: dict[str, dict] = {}
        for t in entry.get("tactics", []):
            name = t["name"]
            line = t.get("line", -1)
            if name not in agg:
                agg[name] = {"count": 0, "line": line}
            agg[name]["count"] += 1
            if line < agg[name]["line"] or agg[name]["line"] == -1:
                agg[name]["line"] = line
        for tname, info in agg.items():
            conn.execute(
                """
                MATCH (d:Decl {name: $decl}), (t:Tactic {name: $tname})
                CREATE (d)-[:USED_TACTIC {line: $line, count: $count}]->(t)
                """,
                {
                    "decl": decl,
                    "tname": tname,
                    "line": info["line"],
                    "count": info["count"],
                },
            )
            n_edges += 1
    return (len(seen), n_edges, len(tac_entries))


def main() -> None:
    decls = load_json(BLUEPRINT_DIR / "decls.json")
    if decls is None:
        raise SystemExit("blueprint/decls.json not found — run `lake exe dumpdecls` first.")

    modules = load_json(BLUEPRINT_DIR / "modules.json") or []
    tactics = load_json(BLUEPRINT_DIR / "tactics.json") or []
    obvious_uses = load_jsonl(BLUEPRINT_DIR / "obvious_uses.jsonl")

    # Idempotent: nuke any existing DB before creating fresh. Kuzu uses a
    # single-file format these days; older versions used a directory.
    if DB_PATH.exists():
        if DB_PATH.is_dir():
            shutil.rmtree(DB_PATH)
        else:
            DB_PATH.unlink()
    for sidecar in BLUEPRINT_DIR.glob("graph.kuzu.*"):
        sidecar.unlink()

    db = kuzu.Database(str(DB_PATH))
    conn = kuzu.Connection(db)

    run_schema(conn)
    n_decls = insert_decls(conn, decls)
    n_mods = insert_modules(conn, modules)
    n_uses = insert_uses_edges(conn, decls)
    n_declared = insert_declared_in(conn, decls, modules)
    n_imports = insert_imports_edges(conn, modules)
    n_tac_nodes, n_tac_edges, n_decls_with_tac = insert_tactics(conn, tactics)
    n_stages, n_obvious_edges, n_orphan = insert_obvious_uses(conn, decls, obvious_uses)

    print(
        f"Ingested: {n_decls} decls, {n_mods} modules, "
        f"{n_uses} USES edges, {n_declared} DECLARED_IN edges, "
        f"{n_imports} IMPORTS edges, "
        f"{n_tac_nodes} tactics in {n_decls_with_tac} decls "
        f"({n_tac_edges} USED_TACTIC edges), "
        f"{n_stages} obvious stages "
        f"({n_obvious_edges} OBVIOUS_USES edges"
        f"{f'; {n_orphan} orphan records' if n_orphan else ''})."
    )


if __name__ == "__main__":
    main()
