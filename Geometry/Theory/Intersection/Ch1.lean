
/- Lemmas relating to intersections using only theory available in Ch1 -/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Insert
import Geometry.Theory.Axioms
import Geometry.Tactics
import Atlas


namespace Geometry.Theory

open Set
open Geometry.Theory
open Atlas

namespace Intersection

atlas commentary := by
  ref lemma 1.0.30
  name "Two pointed intersections of the same line pair share their point"
  preface "If two lines intersect, their intersection is unique."

atlas lemma 1.0.30 "Two pointed intersections of the same line pair share their point"
  : (L intersects M at X) ∧ (L intersects M at Y) -> X = Y := by
  unfold Intersects
  intro ⟨LMatX, LMatY⟩
  rw [LMatX] at LMatY
  exact singleton_eq_singleton_iff.mp LMatY


atlas commentary := by
  ref lemma 1.0.31
  name "Pointed intersection is symmetric in its line arguments"
  preface "L intersects M is the same as M intersects L."

atlas lemma 1.0.31 "Pointed intersection is symmetric in its line arguments"
  : (L intersects M at X) ↔ (M intersects L at X) := by
  unfold Intersects
  refine Eq.congr ?_ rfl
  exact inter_comm L M

attribute [symm] «Pointed intersection is symmetric in its line arguments»

/-- Dot-notation wrapper: `h.symm` swaps the line args of an `L intersects M at X`
    hypothesis. Picks up the `@[symm]` Iff form above via projection. -/
@[symm] def Intersects.symm {L M : Set Point} {X : Point}
  (h : L intersects M at X) : M intersects L at X :=
  («Pointed intersection is symmetric in its line arguments»).mp h


atlas commentary := by
  ref lemma 1.0.32
  name "A pointed intersection's witness point lies on the left line"
  preface "If L intersects M at X, then X is on L"

atlas lemma 1.0.32 "A pointed intersection's witness point lies on the left line"
  : (L intersects M at X) -> (X on L) := by
  unfold Intersects
  intro LMintX
  have XinLintM : X ∈ L ∩ M := by simp_all only [mem_singleton_iff]
  exact mem_of_mem_inter_left XinLintM


atlas commentary := by
  ref lemma 1.0.33
  name "A pointed intersection's witness point lies on the right line"
  preface "If L intersects M at X, then X is on M"

atlas lemma 1.0.33 "A pointed intersection's witness point lies on the right line"
  : (L intersects M at X) -> (X on M) := by
  unfold Intersects
  intro LMintX
  have XinLintM : X ∈ L ∩ M := by simp_all only [mem_singleton_iff]
  exact mem_of_mem_inter_right XinLintM


atlas commentary := by
  ref lemma 1.0.34
  name "A pointed intersection's witness point lies on both lines"
  preface "If L intersects M at X, then X is on L and M"

atlas lemma 1.0.34 "A pointed intersection's witness point lies on both lines"
  : (L intersects M at X) -> (X on L) ∧ (X on M) := by intro inter; exact ⟨ref lemma 1.0.32 inter, ref lemma 1.0.33 inter⟩


atlas commentary := by
  ref lemma 1.0.35
  name "On distinct lines crossing at X every other point on L is off M"
  preface "If L intersects M at X, then forall P not equal to X, if P on L, then P off M."

atlas lemma 1.0.35 "On distinct lines crossing at X every other point on L is off M"
  : (L ≠ M) ∧ (L intersects M at X) -> (∀ P : Point, (P ≠ X) ∧ (P on L) -> (P off M)) := by
  intro ⟨LneM, LintMatX⟩ P ⟨PneX, PonL⟩
  unfold Intersects at LintMatX
  by_contra! PonM
  have PinLintM : P ∈ (L ∩ M) := ⟨PonL, PonM⟩
  rw [LintMatX] at PinLintM
  contradiction


end Intersection

end Geometry.Theory

