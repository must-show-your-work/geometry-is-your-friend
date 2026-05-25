import Aesop
import Mathlib.Logic.ExistsUnique

import Mathlib.Tactic.Basic
import Mathlib.Tactic.ByCases
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Ext
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.Use
import Mathlib.Tactic.WLOG
import Mathlib.Tactic.Contrapose

import Mathlib.Data.Set.Pairwise.Basic
import Mathlib.Data.List.Basic

-- Atlas-refs panel widget: auto-wraps every tactic-bodied `atlas <kind>`
-- proof with `with_atlas_refs`, surfacing the citation list in the
-- InfoView. Imported here (not in a leaf module) so the macro_rules
-- override applies project-wide before any atlas command elaborates.
import Geometry.AtlasRefs

/-- Simp set for `obvious` — see `Geometry/Theory/Axioms.lean` for the
    macro that uses it. Tag chapter-by-chapter as you encounter
    canonical normalizations that Greenberg treats as background.

    Lean requires `register_simp_attr` and `attribute [obvious]` to
    live in *separate* files, hence the registration lives here while
    the actual tagging happens in `Axioms.lean` and downstream.

    The attribute name `obvious` deliberately shadows nothing: tactics
    and attributes live in disjoint namespaces, so `@[obvious]` on a
    decl and `obvious` in tactic mode coexist without ambiguity. -/
register_simp_attr obvious

/-- Stage-specific simp set used by `obvious`'s `unfold Parallel` stage.
    Tag with `@[obvious.parallel]` any reducible def whose unfolding is
    safe-but-expensive (so we don't want it in the main `obvious` set).
    The macro-hygiene escape hatch — `simp only [obvious.parallel]` in
    the cascade resolves the set name without needing to escape the
    underlying constant identifiers.

    Sibling stage-sets follow the `obvious.<class>` convention
    (`obvious.betweenness`, `obvious.incidence`, etc.) as they're added.
    Each tag is, in effect, "what Greenberg considers obvious in the
    context of the topic" — the class-of-intuition framing. -/
register_simp_attr obvious.parallel

/-- Stage-specific simp set for `obvious`'s `unfold Intersects` stage.
    Pointed-intersection facts that need the `Intersects` def opened —
    `1.0.30 .. 1.0.33`, witness-on-left / -right etc. -/
register_simp_attr obvious.intersects

/-- Stage-specific simp set for `obvious`'s `unfold Guards` stage.
    `Guards` / `Splits` reasoning: same-side / opposite-side facts about
    a line `L` and points `A B`. `Splits := ¬Guards` so this set
    typically covers both. -/
register_simp_attr obvious.guards

-- Note: dump-deps tracking for `obvious` is gated on the env var
-- `GIYF_DUMP_DEPS=1` (checked at tactic runtime via `IO.getEnv`).
-- Custom Lean options can't be set via Lake's `-D` flag because
-- Lake doesn't know about them at command-line-parse time; env vars
-- sidestep that. See `Geometry/Tactics/Obvious.lean` for the writer.

