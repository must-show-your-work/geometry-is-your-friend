import Geometry.Tactics
import Geometry.Theory.Primitives
import Geometry.Theory.Constructors
import Geometry.Tactics.NormalizeEq
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Insert

/-!
# `obvious` tactic

Captures the author's intuition for 'by definition' in the text: unfolds
common geometric objects, runs `simp_all` over the `obvious` simp set, and
falls back to `tauto` / Finset-extensionality.

The `obvious` simp set itself is registered in `Geometry/Tactics.lean`
(Lean requires `register_simp_attr` and the first `attribute [obvious]`
use to live in different files). This file populates the set with the
chapter-0 / axiom-level lemmas Greenberg treats as background.
-/

namespace Geometry.Theory

-- `register_simp_attr obvious` lives in `Geometry/Tactics.lean`
-- (Lean requires the registration to be in a different file from the
-- first `attribute [obvious]` use). This block tags the
-- chapter-0 / axiom-level lemmas that count as Greenberg's
-- minimum-standard intuition. Tag conservatively: a bad simp rule
-- here propagates to every `obvious` invocation downstream.

attribute [obvious]
  -- set
  Set.mem_setOf_eq Set.mem_union Set.mem_inter_iff Set.mem_singleton_iff
  -- finset
  Finset.mem_insert Finset.mem_singleton Finset.mem_erase Finset.notMem_empty
  -- propositional
  ne_eq true_or or_true false_or or_false or_self
  true_and and_true false_and and_false and_self
  not_true_eq_false not_false_eq_true not_or not_and not_not

attribute [obvious]
  -- line parts: `mem_def` simp lemmas bridge `P ∈ segment A B` to the
  -- underlying disjunction. (The old setup tagged the `Segment`/etc.
  -- defs themselves; with the typed-structure rewrite they're no longer
  -- defs, and the `@[simp, obvious]` `mem_def` lemmas live next to the
  -- structures in `Geometry/Theory/Constructors.lean`.)
  -- subset unfolding so simple subset goals reduce to pointwise membership.
  Set.subset_def
  -- split a subset-of-intersection into two subsets upfront so simp_all
  -- gets bite-sized goals instead of trying to unfold the whole intersection
  -- pointwise. Cheap rewrite that prevents the explosion observed on
  -- `s ⊆ t ∩ u` goals.
  Set.subset_inter_iff

-- Title-form `@[obvious]` tags for the betweenness axioms (e.g.
-- `«Betweenness Commutativity»`, `«A-B-C implies …»`) live in
-- `Geometry.Theory.Axioms.Betweenness` itself, applied after each
-- decl — that file imports this one, and tagging there avoids a
-- circular import.

/-- Attempts to unfold any geometric objects in the vicinity and eliminate booleans
 and the like. Tries to capture the author's intuition for 'by definition' in the text.

 The last alternative handles Finset literal equality (`{A,B,C} = {C,A,B}` etc.) by
 reducing to membership and tautology — convenient since Finsets are unordered.

 `normalize_eq` runs first to canonicalize `=` / `≠` orientations so `simp_all` can
 close hypotheses regardless of which side they were originally written on.

 The simp set is the `obvious` attribute — each chapter tags its
 own canonical normalizations and they accumulate progressively. -/
macro "obvious" : tactic =>
  `(tactic| (
      try intros
      normalize_eq
      first
      -- Pure rewrite closes the goal entirely (definitional only).
      | (simp_all only [obvious]; done)
      -- Rewrite hyps and goal via `obvious`, then let `tauto` do
      -- the propositional closing. This handles patterns like:
      --   hyp: `A - P - B`  ⊢  `P ∈ LineThrough B A`
      -- where the rewrite turns the hyp into a form that matches one
      -- disjunct of the unfolded goal, and `tauto` picks it.
      | (simp_all only [obvious]; tauto)
      -- Goal-only unfold + propositional close (some sites have hyps
      -- in normalized form already). Uses the typed-structure `mem_def`
      -- lemmas to expose the underlying disjunction.
      | (simp only [Segment.mem_def, Ray.mem_def, Extension.mem_def, LineThrough.mem_def]; tauto)
      -- Last-ditch: simp through the mem_def bridges everywhere and tauto.
      | (simp only [Segment.mem_def, Ray.mem_def, Extension.mem_def, LineThrough.mem_def] at *; tauto)
      -- The `ext` alternative is for Finset-literal equality goals
      -- (`{A,B,C} = {C,A,B}`). Guard with `first` so a `fail`
      -- alternative gives a clean error message when nothing closed.
      | (first
          | (ext; simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_erase, ne_eq]; tauto)
          | fail "obvious: no alternative closed the goal")))

macro "obvious" : term => `(by obvious)

/-! ## Examples -/

section Examples
-- Endpoint membership unfolds via the `Segment` simp tag.
example (A B : Point) : A on segment A B := by obvious
example (A B : Point) : B on segment A B := by obvious

-- Term-position form.
example (A B : Point) : A on segment A B := obvious
end Examples

end Geometry.Theory
