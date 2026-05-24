// Kuzu schema for the Geometry theorem graph.
// Re-runnable: ingest.py drops and recreates before each load.

CREATE NODE TABLE Decl(
    name STRING PRIMARY KEY,
    kind STRING,
    type_raw STRING,
    type_pp STRING,
    doc STRING,
    namespace STRING,
    file STRING,
    line_start INT64,
    line_end INT64,
    has_sorry BOOLEAN,
    is_proposition BOOLEAN,
    is_noncomputable BOOLEAN,
    // Atlas attribute metadata (nullable; populated when @[atlas …] is set
    // — typically via the `atlas <kind>` command macros in Atlas.lean).
    atlas_kind STRING,
    atlas_number STRING,
    atlas_title STRING
);

CREATE NODE TABLE Module(
    name STRING PRIMARY KEY,
    file STRING
);

CREATE NODE TABLE Tactic(
    name STRING PRIMARY KEY
);

// Term-level dependency: a constant referenced inside another's value/proof.
CREATE REL TABLE USES(FROM Decl TO Decl);

// Declaration-to-module association.
CREATE REL TABLE DECLARED_IN(FROM Decl TO Module);

// Module-level import edge (distinct from term-level USES).
CREATE REL TABLE IMPORTS(FROM Module TO Module);

// Tactic occurrence inside a declaration's proof body.
// `count` aggregates multiple uses; `line` is the first occurrence.
CREATE REL TABLE USED_TACTIC(FROM Decl TO Tactic, line INT64, count INT64);

// `obvious`-cascade stages — `simp_all`, `unfold Parallel`,
// `unfold Intersects`, `unfold Guards`, `mem_def goal`, `mem_def at*`,
// `Finset ext`. Populated from blueprint/obvious_uses.jsonl when the
// project is built with `GIYF_DUMP_DEPS=1`.
CREATE NODE TABLE ObviousStage(name STRING PRIMARY KEY);

// Decl `d` closed an `obvious` invocation via `(stage, closer)`. `count`
// aggregates multiple invocations within the same decl that fired the
// same (stage, closer) pair. The closer (`done` / `tauto` / `assumption`
// / `decide` / `aesop`) is the tactic that ultimately closed after the
// stage's preamble ran.
CREATE REL TABLE OBVIOUS_USES(FROM Decl TO ObviousStage, closer STRING, count INT64);
