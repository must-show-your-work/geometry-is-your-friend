
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Insert

import Geometry.Theory.Axioms
import Geometry.Theory.Ch1
import Geometry.Theory.Line.Ch2

import Geometry.Tactics

import Geometry.Ch2.Prop

namespace Geometry.Theory

open Set
open Geometry.Theory
open Geometry.Ch2.Prop

namespace Intersection

instance {L M : Line} {X : Point} : Coe (Intersects L M X) (X ∈ L ∩ M) where
  coe h := by
    unfold Intersects at h
    rw [h]
    exact Set.mem_singleton X

/-- No points are contained on the intersection of a segment and it's related extension -/
lemma seg_inter_ext_empty : segment A B ∩ extension A B = ∅ := by
  unfold Segment; unfold Extension
  ext P
  constructor
  -- Forward case.
  · simp only [ne_eq, mem_inter_iff, mem_setOf_eq, mem_empty_iff_false, imp_false, not_and,
    not_not] ; intro opts ABP AneP
    rcases opts with APB | AeqP | BeqP
    · exfalso ; exact Betweenness.absurdity_abc_acb ⟨ABP, APB⟩
    · contradiction
    · exact BeqP
  -- Reverse
  · simp only [mem_empty_iff_false, ne_eq, mem_inter_iff, mem_setOf_eq, IsEmpty.forall_iff]

/-- Points on a segment are not included in the related extension -/
lemma seg_inter_ext_empty' : X on segment A B -> X off extension A B := by
  intro XonAB
  by_contra! hNeg
  have interEmpty : segment A B ∩ extension A B = ∅ := seg_inter_ext_empty
  have XinInter : X ∈ (segment A B ∩ extension A B) := by tauto
  rw [interEmpty] at XinInter
  contradiction

/-- Points on an extension are off the related segment -/
lemma ext_inter_seg_empty : X on extension A B -> X off segment A B := by
  intro XonAB
  by_contra! hNeg
  have interEmpty : segment A B ∩ extension A B = ∅ := seg_inter_ext_empty
  have XinInter : X ∈ (segment A B ∩ extension A B) := by tauto
  rw [interEmpty] at XinInter
  contradiction

/-- If L and M are distinct, nonparallel lines, and X and Y are found in their intersection, X and Y are equal -/
lemma intersection_is_unique : ∀ L M : Line, L ≠ M -> (L ∦ M) -> X ∈ L ∩ M ∧ Y ∈ L ∩ M -> X = Y := by
  intro L M LneM LnparM ⟨XonInt, YonInt⟩
  have ⟨P, LinterMatP, Puniq⟩ : ∃! X : Point, L intersects M at X := Ch2.Prop.P1 LneM LnparM
  specialize LinterMatP
  rw [LinterMatP] at XonInt
  rw [LinterMatP] at YonInt
  have XeqP : X = P := by tauto
  have YeqP : Y = P := by tauto
  rw [XeqP, YeqP]

/-- If L and M are distinct, parallel lines, their intersection is empty -/
lemma parallel_intersection_is_empty : ∀ L M : Line, (L ≠ M) -> (L ∥ M) -> L ∩ M = ∅ := by
  intro L M LneM LparM
  apply Subset.antisymm
  · tauto
  · tauto

/-- Intersections of distinct, nonparallel lines contain exactly one point -/
lemma single_point_of_intersection : ∀ P : Point, ∀ L M : Line, L ≠ M ∧ (L ∦ M) -> (P ∈ L ∩ M ↔ L intersects M at P) := by
  intro P L M ⟨LneM, LnparM⟩
  constructor
  · intro PinInter
    unfold Intersects
    apply Subset.antisymm
    · intro Q QinInter
      have h := intersection_is_unique L M LneM LnparM ⟨QinInter, PinInter⟩
      trivial
    · intro Q QisP
      have QeqP : Q = P := by tauto
      rw [QeqP]; exact PinInter
  · intro LintMatP
    rw [LintMatP]
    trivial

/-- If a line intersects a segment, then it intersects the ray containing that segment -/
-- TODO: I think some of the non-equality conditions are provable in general.
lemma lift_seg_ray :
  (A ≠ B) -> (L intersects segment A B at X) -> (L intersects ray A B at X) := by
  intro AneB LintABatX
  have XonSegAB : X on segment A B := inter_touch_right LintABatX
  have XonL : X on L := inter_touch_left LintABatX
  have XonRayAB : X on ray A B := by unfold Ray; tauto
  have LneRayAB : L ≠ ray A B := by
    by_contra! hNeg
    rw [hNeg] at LintABatX
    unfold Intersects at LintABatX
    have AonSegAB : A on segment A B := by tauto
    have AonRayAB : A on ray A B := by unfold Ray; tauto
    have AonIntRaySeg : A ∈ ray A B ∩ segment A B := by tauto
    rw [LintABatX] at AonIntRaySeg
    have AeqX : A = X := by tauto
    have BonSegAB : B on segment A B := by tauto
    have BonRayAB : B on ray A B := by unfold Ray; tauto
    have BonIntRaySeg : B ∈ ray A B ∩ segment A B := by tauto
    rw [LintABatX] at BonIntRaySeg
    have BeqX : B = X := by tauto
    have AeqB : A = B := by rw [BeqX, AeqX]
    contradiction
  have LnparRayAB : L ∦ ray A B := by tauto
  -- assume there is some point not X that intersects the ray.
  by_cases counter : ∃ P : Point, (L intersects ray A B at P) ∧ (P ≠ X)
  · obtain ⟨P, LintRayABatP, PneX⟩ := counter
    have XinInter : X ∈ L ∩ ray A B := by tauto
    unfold Intersects at LintRayABatP
    rw [LintRayABatP] at XinInter
    have XeqP : P = X := by tauto
    contradiction
  · push_neg at counter
    apply Subset.antisymm
    · intro P PonLintRay
      have XonLintRay : X ∈ L ∩ ray A B := by tauto
      have PeqX : P = X := intersection_is_unique L (ray A B) LneRayAB LnparRayAB ⟨PonLintRay, XonLintRay⟩
      rw [PeqX]
      trivial
    · intro P PinSingleX
      have PeqX : P = X := by tauto
      rw [PeqX]; trivial

/-- If L intersects M anywhere, then L cannot be parallel to M -/
lemma intersections_are_not_parallel : (L intersects M at P) -> (L ∦ M) := by
  intro LintMatP
  unfold Parallel
  push_neg
  intro LneM
  use P
  unfold Intersects at LintMatP
  simp_all only [Line.coincidence_is_coincidence_of_all_points, mem_inter_iff, mem_singleton_iff, ne_eq, not_forall]

/-- If a line intersects a ray, then it intersects the line containing the ray -/
lemma lift_ray_line {AneB : A ≠ B} : (L intersects ray A B at X) -> (L intersects line A B at X) := by
  intro LintRay
  have XonRayAB : X on ray A B := inter_touch_right LintRay
  have XonL : X on L := inter_touch_left LintRay
  have XABCol := @Line.all_points_on_a_ray_are_collinear A B X AneB XonRayAB
  have XonLineAB : X on line A B := Line.ray_sub_line XonRayAB
  have XonRayAB : X on ray A B := by tauto
  have XinInter : X ∈ L ∩ line A B := by tauto
  have LnparRayAB : L ∦ ray A B := intersections_are_not_parallel LintRay
  have LnparLineAB : L ∦ line A B := by
    unfold Parallel
    push_neg
    intro LneLineAB
    use X
  have LneRayAB := Ne.symm (Line.line_is_bigger_than_ray L A B AneB)
  have LneLineAB : L ≠ line A B := by
    by_contra! hNeg
    have AonLineAB : A on line A B := Line.line_has_definition_points.left
    have AonRayAB : A on ray A B := Line.ray_has_endpoints.left
    have AonL : A on L := by rw [<- hNeg] at AonLineAB; tauto
    have BonLineAB : B on line A B := Line.line_has_definition_points.right
    have BonRayAB : B on ray A B := Line.ray_has_endpoints.right
    have BonL : B on L := by rw [<- hNeg] at BonLineAB; tauto
    have AinIntLine : A ∈ L ∩ line A B := by tauto
    have BinIntLine : B ∈ L ∩ line A B := by tauto
    have AinIntRay : A ∈ L ∩ ray A B := by tauto
    have BinIntRay : B ∈ L ∩ ray A B := by tauto
    have LintABatA : L intersects ray A B at A := (single_point_of_intersection A L (Ray A B) ⟨LneRayAB, LnparRayAB⟩).mp AinIntRay
    have LintABatB : L intersects ray A B at B := (single_point_of_intersection B L (Ray A B) ⟨LneRayAB, LnparRayAB⟩).mp BinIntRay
    unfold Intersects at *
    rw [LintRay] at LintABatA
    rw [LintRay] at LintABatB
    rw [LintABatB] at LintABatA
    simp only [singleton_eq_singleton_iff] at LintABatA
    rw [LintABatA] at AneB
    contradiction
  by_cases counter : ∃ P : Point, (L intersects line A B at P) ∧ (P ≠ X)
  · obtain ⟨P, LintABatP, PneX⟩ := counter
    have PinInter : P ∈ L ∩ line A B := by
      rw [LintABatP]
      trivial
    have PeqX : P = X := intersection_is_unique L (line A B) LneLineAB LnparLineAB ⟨PinInter, XinInter⟩
    contradiction
  · push_neg at counter
    apply Subset.antisymm
    · intro P PinInter
      exact counter P ((single_point_of_intersection P L (line A B) ⟨LneLineAB, LnparLineAB⟩).mp PinInter)
    · intro P PisX
      have PeqX : P = X := by tauto
      rw [PeqX]
      trivial

/-- If a line intersects a segment, then it intersects the line containing the segment -/
lemma lift_seg_line {AneB : A ≠ B} : (L intersects segment A B at X) -> (L intersects line A B at X) := by
  intro LintSeg
  apply lift_seg_ray at LintSeg
  apply lift_ray_line at LintSeg
  exact LintSeg
  repeat exact AneB

/-- If A - X - B, and L intersects a segment A B at X, then L splits A and B -/
lemma splits_points {L : Line} {A X B : Point} (AXB : A - X - B) :
  (L intersects M at X) -> (L splits A and B) := by
  intro LintAXBatX
  unfold SameSide
  push_neg
  intro AoffL BoffL
  have distinctAXB := Betweenness.abc_imp_distinct AXB
  distinguish
  use X
  constructor
  · unfold Segment; simp only [mem_setOf_eq]; left; exact AXB
  · exact Intersection.inter_touch_left LintAXBatX

/-- If L intersect M at X, and A is not X, then either A is off L or M or both. -/
lemma miss_means_off {L M : Line} {A X : Point} : A ≠ X -> (L intersects M at X) -> (A off L) ∨ (A off M) := by
  intro AneX LintMatX
  by_contra! AonLandM
  have AinInt : A ∈ L ∩ M := AonLandM
  rw [LintMatX] at AinInt
  tauto


/-- Let L and M be lines, with A and B on L. If L intersects M at some X not A or B; and
  if M splits A and B, then A - X - B 

  ED: This extracts the common argument at the end of p3.3 and it's corollaries.
-/
lemma between_splits
  (AneX : A ≠ X) (BneX : B ≠ X) :
  (L intersects M at X) -> (A on L ∧ B on L) -> (M splits A and B) -> (A - X - B) := by
  intro LintMatX ⟨AonL, BonL⟩ MsplitsAB
  have ⟨AoffM, BoffM⟩  : (A off M) ∧ (B off M) := by
    have hA := miss_means_off AneX LintMatX
    have hB := miss_means_off BneX LintMatX
    tauto
  unfold SameSide at MsplitsAB; push_neg at MsplitsAB
  specialize MsplitsAB AoffM BoffM
  obtain ⟨AneB, P, PonSeg, PonM⟩ := MsplitsAB
  -- L and line A B are the same thing since two points determine a line.
  have LeqAB : L = line A B := Line.equiv AneB ⟨AonL, Line.line_has_definition_points.left, BonL, Line.line_has_definition_points.right⟩
  -- so P on L
  have PonL : P on L := by
    apply Line.seg_sub_line at PonSeg
    rw [<- LeqAB] at PonSeg
    trivial
  -- since P on L and P on M, P = X
  have PeqX : P = X := by
    have PinLintM : P ∈ L ∩ M := by tauto
    rw [LintMatX] at PinLintM
    tauto
  -- so now we just dispatch the cases
  rcases PonSeg with APB | AeqP | BeqP
  · rw [PeqX] at APB; exact APB
  · rw [PeqX] at AeqP ; contradiction
  · rw [PeqX] at BeqP ; contradiction

/-- If X is on a line L, and E is not on L, then:
  1. L and EX are distinct lines
  2. L and EX are not parallel
  3. L intersects EX at X -/
lemma auxillary_line_through {L : Line} {X E : Point} (XonL : X on L) (EoffL : E off L)
    : (L ≠ (line E X)) ∧ (L ∦ (line E X)) ∧ (L intersects (line E X) at X) := by
  have XonEX : X on (line E X) := Line.line_has_definition_points.right
  have EonEX : E on (line E X) := Line.line_has_definition_points.left
  have ne : L ≠ (line E X) := by
    by_contra! hNeg; rw [hNeg] at EoffL; contradiction
  have npar : L ∦ (line E X) := by
    intro hpar
    have XinInter : X ∈ L ∩ (line E X) := ⟨XonL, XonEX⟩
    rw [Intersection.parallel_intersection_is_empty L (line E X) (by tauto) hpar] at XinInter
    exact absurd XinInter (Set.notMem_empty X)
  have XonLintEX : X ∈ L ∩ (line E X) := by tauto
  have int : L intersects (line E X) at X := (single_point_of_intersection X L (line E X) ⟨ne, npar⟩).mp XonLintEX
  tauto

/-- If A, B, and Z are on L, a line M passes through L at Z, and Z is not between A and B, then M guards A and B. -/
lemma guards_when_not_between {L M : Line} {Z A B : Point}
    (AneZ : A ≠ Z) (BneZ : B ≠ Z)
    (LintMatZ : L intersects M at Z)
    (onL : A on L ∧ B on L)
    (notAZB : ¬(A - Z - B))
    : M guards A and B := by
  rcases LotEMGuards with split | guard
  · exact absurd (Intersection.between_splits AneZ BneZ LintMatZ onL split) notAZB
  · exact guard

end Intersection

end Geometry.Theory
