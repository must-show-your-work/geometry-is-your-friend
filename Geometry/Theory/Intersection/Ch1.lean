
/- Lemmas relating to intersections using only theory available in Ch1 -/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Insert
import Geometry.Theory.Axioms
import Geometry.Tactics


namespace Geometry.Theory

open Set
open Geometry.Theory

namespace Intersection

/-- If two lines intersect, their intersection is unique. -/
lemma uniq : (L intersects M at X) ∧ (L intersects M at Y) -> X = Y := by
  unfold Intersects
  intro ⟨LMatX, LMatY⟩
  rw [LMatX] at LMatY
  exact singleton_eq_singleton_iff.mp LMatY

/-- L intersects M is the same as M intersects L. -/
lemma symm : (L intersects M at X) ↔ (M intersects L at X) := by
  unfold Intersects
  refine Eq.congr ?_ rfl
  exact inter_comm L M

/-- If L intersects M at X, then X is on L -/
lemma inter_touch_left : (L intersects M at X) -> (X on L) := by
  unfold Intersects
  intro LMintX
  have XinLintM : X ∈ L ∩ M := by simp_all only [mem_singleton_iff]
  exact mem_of_mem_inter_left XinLintM

/-- If L intersects M at X, then X is on M -/
lemma inter_touch_right : (L intersects M at X) -> (X on M) := by
  unfold Intersects
  intro LMintX
  have XinLintM : X ∈ L ∩ M := by simp_all only [mem_singleton_iff]
  exact mem_of_mem_inter_right XinLintM

/-- If L intersects M at X, then X is on L and M -/
lemma inter_touch : (L intersects M at X) -> (X on L) ∧ (X on M) := by intro inter; exact ⟨inter_touch_left inter, inter_touch_right inter⟩

/-- If L intersects M at X, then forall P not equal to X, if P on L, then P off M. -/
lemma uniq_solitary : (L ≠ M) ∧ (L intersects M at X) -> (∀ P : Point, (P ≠ X) ∧ (P on L) -> (P off M)) := by
  intro ⟨LneM, LintMatX⟩ P ⟨PneX, PonL⟩
  unfold Intersects at LintMatX
  by_contra! PonM
  have PinLintM : P ∈ (L ∩ M) := by tauto
  rw [LintMatX] at PinLintM
  contradiction

end Intersection

end Geometry.Theory

