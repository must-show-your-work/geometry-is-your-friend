
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Insert

import Geometry.Theory.Axioms
import Geometry.Theory.Ch1
import Geometry.Theory.Line.Ch2

import Geometry.Tactics

import Geometry.Ch2.Prop
import Atlas

namespace Geometry.Theory

open Set
open Geometry.Theory
open Geometry.Ch2.Prop
open Atlas

namespace Intersection

instance {L M : Line} {X : Point} : Coe (Intersects L M X) (X ∈ L ∩ M) where
  coe h := by
    unfold Intersects at h
    rw [h]
    exact Set.mem_singleton X

atlas commentary := by
  ref lemma 2.0.15
  name "Segment A B and the related extension A B have empty intersection"
  preface "No points are contained on the intersection of a segment and it's related extension"

atlas lemma 2.0.15 "Segment A B and the related extension A B have empty intersection"
  : (segment A B : Set Point) ∩ (extension A B : Set Point) = ∅ := by
  ext P
  constructor
  -- Forward case.
  · simp only [ne_eq, mem_inter_iff, Segment.carrier, Extension.carrier, mem_setOf_eq,
      mem_empty_iff_false, imp_false, not_and, not_not] ; intro opts ABP AneP
    rcases opts with APB | AeqP | BeqP
    · exfalso ; exact ref lemma 1.0.37 ⟨ABP, APB⟩
    · contradiction
    · exact BeqP
  -- Reverse
  · simp only [mem_empty_iff_false, ne_eq, mem_inter_iff, Segment.carrier, Extension.carrier,
      mem_setOf_eq, IsEmpty.forall_iff]


atlas commentary := by
  ref lemma 2.0.16
  name "A point on a segment lies off the related extension"
  preface "Points on a segment are not included in the related extension"

atlas lemma 2.0.16 "A point on a segment lies off the related extension"
  : X on segment A B -> X off extension A B := by
  intro XonAB
  by_contra! hNeg
  have interEmpty : (segment A B : Set Point) ∩ (extension A B : Set Point) = ∅ := ref lemma 2.0.15
  have XinInter : X ∈ ((segment A B : Set Point) ∩ (extension A B : Set Point)) := by tauto
  rw [interEmpty] at XinInter
  contradiction


atlas commentary := by
  ref lemma 2.0.17
  name "A point on an extension lies off the related segment"
  preface "Points on an extension are off the related segment"

atlas lemma 2.0.17 "A point on an extension lies off the related segment"
  : X on extension A B -> X off segment A B := by
  intro XonAB
  by_contra! hNeg
  have interEmpty : (segment A B : Set Point) ∩ (extension A B : Set Point) = ∅ := ref lemma 2.0.15
  have XinInter : X ∈ ((segment A B : Set Point) ∩ (extension A B : Set Point)) := by tauto
  rw [interEmpty] at XinInter
  contradiction


atlas commentary := by
  ref lemma 2.0.18
  name "Two points in the intersection of distinct nonparallel lines coincide"
  preface "If L and M are distinct, nonparallel lines, and X and Y are found in their intersection, X and Y are equal"

atlas lemma 2.0.18 "Two points in the intersection of distinct nonparallel lines coincide"
  : ∀ L M : Line, L ≠ M -> (L ∦ M) -> X ∈ L ∩ M ∧ Y ∈ L ∩ M -> X = Y := by
  intro L M LneM LnparM ⟨XonInt, YonInt⟩
  have ⟨P, LinterMatP, Puniq⟩ : ∃! X : Point, L intersects M at X := proposition 2.1 LneM LnparM
  specialize LinterMatP
  rw [LinterMatP] at XonInt
  rw [LinterMatP] at YonInt
  have XeqP : X = P := by tauto
  have YeqP : Y = P := by tauto
  rw [XeqP, YeqP]


atlas commentary := by
  ref lemma 2.0.19
  name "The intersection of two distinct parallel lines is empty"
  preface "If L and M are distinct, parallel lines, their intersection is empty"

atlas lemma 2.0.19 "The intersection of two distinct parallel lines is empty"
  : ∀ L M : Line, (L ≠ M) -> (L ∥ M) -> L ∩ M = ∅ := by
  intro L M LneM LparM
  apply Subset.antisymm
  · tauto
  · tauto


atlas commentary := by
  ref lemma 2.0.20
  name "Membership in the intersection of distinct nonparallel lines is the pointed intersection"
  preface "Intersections of distinct, nonparallel lines contain exactly one point"

atlas lemma 2.0.20 "Membership in the intersection of distinct nonparallel lines is the pointed intersection"
  : ∀ P : Point, ∀ L M : Line, L ≠ M ∧ (L ∦ M) -> (P ∈ L ∩ M ↔ L intersects M at P) := by
  intro P L M ⟨LneM, LnparM⟩
  constructor
  · intro PinInter
    unfold Intersects
    apply Subset.antisymm
    · intro Q QinInter
      have h := ref lemma 2.0.18 L M LneM LnparM ⟨QinInter, PinInter⟩
      trivial
    · intro Q QisP
      have QeqP : Q = P := by tauto
      rw [QeqP]; exact PinInter
  · intro LintMatP
    rw [LintMatP]
    trivial


atlas commentary := by
  ref lemma 2.0.21
  name "A line intersecting a segment intersects its containing ray at the same point"
  preface "If a line intersects a segment, then it intersects the ray containing that segment"
  notes "TODO: I think some of the non-equality conditions are provable in general."

atlas lemma 2.0.21 "A line intersecting a segment intersects its containing ray at the same point"
  : (A ≠ B) -> (L intersects segment A B at X) -> (L intersects ray A B at X) := by
  intro AneB LintABatX
  have XonSegAB : X on segment A B := ref lemma 1.0.33 LintABatX
  have XonL : X on L := ref lemma 1.0.32 LintABatX
  have XonRayAB : X on ray A B := by obvious
  have LneRayAB : L ≠ (ray A B : Set Point) := by
    by_contra! hNeg
    rw [hNeg] at LintABatX
    unfold Intersects at LintABatX
    have AonSegAB : A on segment A B := by obvious
    have AonRayAB : A on ray A B := by obvious
    have AonIntRaySeg : A ∈ ((ray A B : Set Point) ∩ (segment A B : Set Point)) := by tauto
    rw [LintABatX] at AonIntRaySeg
    have AeqX : A = X := by tauto
    have BonSegAB : B on segment A B := by obvious
    have BonRayAB : B on ray A B := by obvious
    have BonIntRaySeg : B ∈ ((ray A B : Set Point) ∩ (segment A B : Set Point)) := by tauto
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
  · push Not at counter
    apply Subset.antisymm
    · intro P PonLintRay
      have XonLintRay : X ∈ L ∩ ray A B := by tauto
      have PeqX : P = X := ref lemma 2.0.18 L (ray A B) LneRayAB LnparRayAB ⟨PonLintRay, XonLintRay⟩
      rw [PeqX]
      trivial
    · intro P PinSingleX
      have PeqX : P = X := by tauto
      rw [PeqX]; trivial


atlas commentary := by
  ref lemma 2.0.22
  name "If two lines have a pointed intersection they are not parallel"
  preface "If L intersects M anywhere, then L cannot be parallel to M"

atlas lemma 2.0.22 "If two lines have a pointed intersection they are not parallel"
  : (L intersects M at P) -> (L ∦ M) := by
  intro LintMatP
  unfold Parallel
  push Not
  intro LneM
  use P
  unfold Intersects at LintMatP
  obvious


atlas commentary := by
  ref lemma 2.0.23
  name "A line intersecting a ray intersects its containing line at the same point"
  preface "If a line intersects a ray, then it intersects the line containing the ray"

atlas lemma 2.0.23 "A line intersecting a ray intersects its containing line at the same point"
  {AneB : A ≠ B} : (L intersects ray A B at X) -> (L intersects line A B at X) := by
  intro LintRay
  have XonRayAB : X on ray A B := ref lemma 1.0.33 LintRay
  have XonL : X on L := ref lemma 1.0.32 LintRay
  -- `@«Title»` form needed: positional implicits.
  have XABCol := @Line.«Ray Points are Collinear» A B X AneB XonRayAB
  have XonLineAB : X on line A B := ref lemma 1.0.18 XonRayAB
  have XonRayAB : X on ray A B := by tauto
  have XinInter : X ∈ L ∩ line A B := by tauto
  have LnparRayAB : L ∦ ray A B := ref lemma 2.0.22 LintRay
  have LnparLineAB : L ∦ line A B := by
    unfold Parallel
    push Not
    intro LneLineAB
    use X
    tauto
  have LneRayAB : L ≠ ray A B := Ne.symm (ref lemma 2.0.12)
  have LneLineAB : L ≠ line A B := by
    by_contra! hNeg
    have AonLineAB : A on line A B := ref lemma 1.0.23
    have AonRayAB : A on ray A B := ref lemma 1.0.21
    have AonL : A on L := by
      have h : A ∈ (line A B : Set Point) := AonLineAB
      rw [<- hNeg] at h; tauto
    have BonLineAB : B on line A B := ref lemma 1.0.24
    have BonRayAB : B on ray A B := ref lemma 1.0.22
    have BonL : B on L := by
      have h : B ∈ (line A B : Set Point) := BonLineAB
      rw [<- hNeg] at h; tauto
    have AinIntLine : A ∈ L ∩ line A B := by tauto
    have BinIntLine : B ∈ L ∩ line A B := by tauto
    have AinIntRay : A ∈ L ∩ ray A B := by tauto
    have BinIntRay : B ∈ L ∩ ray A B := by tauto
    have LintABatA : L intersects ray A B at A := (ref lemma 2.0.20 A L (ray A B : Set Point) ⟨LneRayAB, LnparRayAB⟩).mp AinIntRay
    have LintABatB : L intersects ray A B at B := (ref lemma 2.0.20 B L (ray A B : Set Point) ⟨LneRayAB, LnparRayAB⟩).mp BinIntRay
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
    have PeqX : P = X := ref lemma 2.0.18 L (line A B) LneLineAB LnparLineAB ⟨PinInter, XinInter⟩
    contradiction
  · push Not at counter
    apply Subset.antisymm
    · intro P PinInter
      exact counter P ((ref lemma 2.0.20 P L (line A B) ⟨LneLineAB, LnparLineAB⟩).mp PinInter)
    · intro P PisX
      have PeqX : P = X := by tauto
      rw [PeqX]
      trivial


atlas commentary := by
  ref lemma 2.0.24
  name "A line intersecting a segment intersects its containing line at the same point"
  preface "If a line intersects a segment, then it intersects the line containing the segment"

atlas lemma 2.0.24 "A line intersecting a segment intersects its containing line at the same point"
  {AneB : A ≠ B} : (L intersects segment A B at X) -> (L intersects line A B at X) := by
  intro LintSeg
  apply ref lemma 2.0.21 at LintSeg
  apply @«A line intersecting a ray intersects its containing line at the same point» A B L X AneB at LintSeg
  exact LintSeg
  exact AneB


atlas commentary := by
  ref lemma 2.0.25
  name "If A-X-B and L meets the segment at X then L splits A and B"
  preface "If A - X - B, and L intersects a segment A B at X, then L splits A and B"

atlas lemma 2.0.25 "If A-X-B and L meets the segment at X then L splits A and B"
  {L : Line} {A X B : Point} (AXB : A - X - B) :
  (L intersects M at X) -> (L splits A and B) := by
  intro LintAXBatX
  unfold Splits Guards
  push Not
  intro AoffL BoffL
  have distinctAXB := ref lemma 1.0.39 AXB
  distinguish
  use X
  constructor
  · simp only [Segment.mem_def]; left; exact AXB
  · exact ref lemma 1.0.32 LintAXBatX

atlas commentary := by
  ref corollary 2.0.25
  name "Drop the strict-betweenness premise from 2.0.25 by case analysis"
  preface "If L intersects segment A B at X (no a priori betweenness assumption on X), then L splits A and B. Generalizes lemma 2.0.25 by handling the endpoint cases (X = A or X = B) via case analysis on the segment trichotomy. Shares number 2.0.25 with the parent lemma — call sites must use `via lemma 2.0.25 …` (type-dispatched across paired decls) rather than `ref lemma 2.0.25 …` (single-match)."

atlas corollary 2.0.25 "If L intersects segment A B at X, then L splits A and B"
  {L : Line} {A B X : Point} :
  (L intersects (segment A B) at X) -> (L splits A and B) := by
    intro LintABatX
    have XonL : X on L := ref lemma 1.0.32 LintABatX
    -- X ∈ Segment A B is the closed-segment trichotomy.
    have hX : (A - X - B) ∨ A = X ∨ B = X := ref lemma 1.0.33 LintABatX
    rcases hX with AXB | AeqX | BeqX
    · exact ref lemma 2.0.25 AXB LintABatX
    · intro Hsame; apply Hsame.1; rw [AeqX]; exact XonL
    · intro Hsame; apply Hsame.2.1; rw [BeqX]; exact XonL


atlas commentary := by
  ref lemma 2.0.26
  name "A point different from the meet of two lines lies off at least one of them"
  preface "If L intersect M at X, and A is not X, then either A is off L or M or both."

atlas lemma 2.0.26 "A point different from the meet of two lines lies off at least one of them"
  {L M : Line} {A X : Point} : A ≠ X -> (L intersects M at X) -> (A off L) ∨ (A off M) := by
  intro AneX LintMatX
  by_contra! AonLandM
  have AinInt : A ∈ L ∩ M := AonLandM
  rw [LintMatX] at AinInt
  tauto



atlas commentary := by
  ref lemma 2.0.27
  name "Crossing point of L through M between A and B forces A-X-B when M splits A B"
  preface "Let L and M be lines, with A and B on L. If L intersects M at some X not A or B; and
  if M splits A and B, then A - X - B"
  notes "This extracts the common argument at the end of p3.3 and it's corollaries."

atlas lemma 2.0.27 "Crossing point of L through M between A and B forces A-X-B when M splits A B"
  (AneX : A ≠ X) (BneX : B ≠ X) :
  (L intersects M at X) -> (A on L ∧ B on L) -> (M splits A and B) -> (A - X - B) := by
  intro LintMatX ⟨AonL, BonL⟩ MsplitsAB
  have ⟨AoffM, BoffM⟩  : (A off M) ∧ (B off M) := by
    have hA := ref lemma 2.0.26 AneX LintMatX
    have hB := ref lemma 2.0.26 BneX LintMatX
    tauto
  unfold Splits Guards at MsplitsAB; push Not at MsplitsAB
  specialize MsplitsAB AoffM BoffM
  obtain ⟨AneB, P, PonSeg, PonM⟩ := MsplitsAB
  -- L and line A B are the same thing since two points determine a line.
  have LeqAB : L = line A B := ref lemma 2.0.2 AneB ⟨AonL, ref lemma 1.0.23, BonL, ref lemma 1.0.24⟩
  -- so P on L
  have PonL : P on L := by
    apply ref lemma 2.0.5 at PonSeg
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


atlas commentary := by
  ref lemma 2.0.28
  name "Through X on L and E off L: L and line E X are distinct, nonparallel, meet at X"
  preface "If X is on a line L, and E is not on L, then:
  1. L and EX are distinct lines
  2. L and EX are not parallel
  3. L intersects EX at X"

atlas lemma 2.0.28 "Through X on L and E off L: L and line E X are distinct, nonparallel, meet at X"
  {L : Line} {X E : Point} (XonL : X on L) (EoffL : E off L)
    : (L ≠ (line E X)) ∧ (L ∦ (line E X)) ∧ (L intersects (line E X) at X) := by
  have XonEX : X on (line E X) := ref lemma 1.0.24
  have EonEX : E on (line E X) := ref lemma 1.0.23
  have ne : L ≠ (line E X) := by
    by_contra! hNeg; rw [hNeg] at EoffL; contradiction
  have npar : L ∦ (line E X) := by
    intro hpar
    have XinInter : X ∈ L ∩ (line E X) := ⟨XonL, XonEX⟩
    rw [ref lemma 2.0.19 L (line E X) (by tauto) hpar] at XinInter
    exact absurd XinInter (Set.notMem_empty X)
  have XonLintEX : X ∈ L ∩ (line E X) := by tauto
  have int : L intersects (line E X) at X := (ref lemma 2.0.20 X L (line E X) ⟨ne, npar⟩).mp XonLintEX
  tauto


atlas commentary := by
  ref lemma 2.0.29
  name "A line crossing L at Z (not between A and B on L) guards A and B"
  preface "If A, B, and Z are on L, a line M passes through L at Z, and Z is not between A and B, then M guards A and B."

atlas lemma 2.0.29 "A line crossing L at Z (not between A and B on L) guards A and B"
  {L M : Line} {Z A B : Point}
    (AneZ : A ≠ Z) (BneZ : B ≠ Z)
    (LintMatZ : L intersects M at Z)
    (onL : A on L ∧ B on L)
    (notAZB : ¬(A - Z - B))
    : M guards A and B := by
  rcases Classical.em (Guards A B M) with guard | split
  · exact guard
  · exact absurd (ref lemma 2.0.27 AneZ BneZ LintMatZ onL split) notAZB


end Intersection

end Geometry.Theory
