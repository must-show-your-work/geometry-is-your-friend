import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Insert

import Geometry.Theory.Axioms
import Geometry.Theory.Interpendices.A

import Geometry.Tactics

import Geometry.Ch2.Prop
import Atlas

namespace Geometry.Theory

open Set
open Geometry.Theory
open Geometry.Ch2.Prop
open Atlas

set_option maxRecDepth 5000

namespace Line

atlas commentary := by
  ref lemma 2.0.1
  name "Line Trichotomy: Two lines either share no points share one point or are equal"
  preface "An intersection is either empty, a singleton, or the lines are equal."
  aliases [
    Geometry.Theory.Line.trichotomy
  ]

atlas lemma 2.0.1 "Two lines either share no points share one point or are equal"
  : ∀ L M : Line, (L ∩ M = ∅) ∨ (∃! X, L ∩ M = {X}) ∨ L = M := by
  intro L M
  by_cases suppose : (L ≠ M) ∧ (L ∦ M)
  · right; left
    exact proposition 2.1 suppose.left suppose.right
  · simp only [not_and_or, not_not] at suppose
    rcases suppose with LeqM | other
    · right; right; exact LeqM
    · left; push Not at *
      obtain ⟨_, LparM⟩ := other
      apply Line.eq_of_subset
      · intro e eInInt
        specialize LparM e
        rw [Line.inter_toSet, Set.mem_inter_iff] at eInInt
        obvious
      · obvious

atlas commentary := by
  ref lemma 2.0.2
  name "Two distinct points on two lines force the lines to coincide"
  preface "If two distinct points are found on two lines, those lines are equal."

atlas lemma 2.0.2 "Two distinct points on two lines force the lines to coincide"
  {L M : Line} {A B : Point} : A ≠ B -> ((A on L) ∧ (A on M) ∧ (B on L) ∧ (B on M) -> L = M) := by
  intro AneB ⟨AonL, AonM, BonL, BonM⟩
  have Aexists : A ∈ L ∩ M := by obvious
  have Bexists : B ∈ L ∩ M := by obvious
  comment "This is a _sweet_ use of trichotomy. This proof was much longer prior to this."
  rcases ref lemma 2.0.1 L M with LparM | LintMatX | LeqM
  · -- the intersection is nonempty by assumption
    exfalso
    rw [LparM] at Aexists
    contradiction
  · obtain ⟨X, Xinter, Xuniq⟩ := LintMatX
    exfalso
    -- A and B are both in the intersection by hypothesis
    rw [Xinter] at Aexists Bexists
    have AeqX : A = X := by obvious
    have BeqX : B = X := by obvious
    rw [AeqX, BeqX] at AneB
    contradiction
  · exact LeqM

attribute [simp] «Two distinct points on two lines force the lines to coincide»

atlas lemma 2.0.3 "Line Commutativity"
  {AneB : A ≠ B} : (line A B : Line) = line B A := by
  suffices subset : ∀ A B : Point, A ≠ B -> (line A B : Line) ⊆ line B A by
    exact Line.eq_of_subset
      (subset A B AneB)
      (subset B A AneB.symm)
  intro A B AneB P PinAB
  rcases PinAB with PeqA | PeqB | APB | ABP | PBA
  · rw [PeqA]; obvious
  · rw [PeqB]; obvious
  all_goals obvious


atlas commentary := by
  ref lemma 2.0.5
  name "Segment A B is a subset of line A B"
  preface "A segment is a subset of the line A B"

atlas lemma 2.0.5 "Segment A B is a subset of line A B"
  : (segment A B : Line) ⊆ (line A B : Line) := by
  have h₁ : (segment A B : Line) ⊆ (ray A B : Line) := obvious
  have h₂ : (ray A B : Line) ⊆ (line A B : Line) := ref lemma 1.0.18
  intro P PonSeg
  rcases PonSeg with APB | AorBeqP
  repeat obvious

atlas commentary := by
  ref lemma 2.0.6
  name "Line Points are Collinear"
  preface "All points on a line are collinear"

atlas lemma 2.0.6 "Line Points are Collinear"
  {AneB : A ≠ B} : P on line A B -> collinear A B P := by
  -- Direct Proof
  intro PonAB
  simp only [LineThrough.mem_def] at PonAB
  rcases PonAB with PeqA | PeqB | tween | tween | tween
  todo "These should be reducible to a single invocation, maybe a suffices?"
  · rw [<- PeqA];
    apply (ref lemma 1.0.17 B P).mpr
    by_cases suppose: B = P
    · rw [<- PeqA, suppose] at AneB; contradiction
    · exact ref lemma 1.0.14 suppose
  · rw [<- PeqB]
    apply (ref lemma 1.0.16 A P).mpr
    by_cases suppose: A = P
    · rw [<- PeqB, suppose] at AneB; contradiction
    · exact ref lemma 1.0.14 suppose
  repeat exact Collinear.order_irrelevance (ref axiom B.1 tween).collinear


atlas commentary := by
  ref lemma 2.0.7
  name "Every point on extension A B is collinear with A and B"
  preface "All points on a extension are collinear"

atlas lemma 2.0.7 "Every point on extension A B is collinear with A and B"
  {A B : Point} : P on extension A B -> collinear A B P := by
  intro PonExtAB
  exact (ref axiom B.1 PonExtAB.left).collinear


atlas commentary := by
  ref lemma 2.0.8
  name "Every point on segment A B is collinear with A and B"
  preface "All points on a segment are collinear"

atlas lemma 2.0.8 "Every point on segment A B is collinear with A and B"
  {AneB : A ≠ B} : P on segment A B -> collinear A B P := by
  intro PonSegAB
  apply ref lemma 2.0.5 at PonSegAB
  exact @«Line Points are Collinear» A B P AneB PonSegAB


atlas commentary := by
  ref lemma 2.0.9
  name "Ray Points are Collinear"
  preface "All points on a ray are collinear"

atlas lemma 2.0.9 "Ray Points are Collinear"
  {AneB : A ≠ B} : P on ray A B -> collinear A B P := by
  intro PonAB
  apply ref lemma 1.0.18 at PonAB
  exact @«Line Points are Collinear» A B P AneB PonAB



atlas lemma 2.0.10 "Segment A B and extension A B are disjoint"
  : (segment A B : Line) ∩ extension A B = ∅ := by
  apply Line.ext_set
  rw [Line.inter_toSet, Line.empty_toSet]
  apply Subset.antisymm
  · intro P ⟨PonSeg, PonExt⟩
    have ⟨ABP, AneP, BneP⟩ := PonExt
    rcases PonSeg with APB | AeqP | BeqP
    · exfalso; exact ref lemma 1.0.37 ⟨ABP, APB⟩
    · contradiction
    · contradiction
  · intro _ absurdity; exfalso; contradiction



atlas commentary := by
  ref lemma 2.0.12
  name "A ray A B is never equal to any line L"
  preface "A line is 'bigger' than a ray in the same way that a line is bigger than a segment"

atlas lemma 2.0.12 "A ray A B is never equal to any line L"
  { L : Line } {A B : Point}  (AneB : A ≠ B := by assumption) : ray A B ≠ L := by
  by_contra ABeqL
  idea "construct a point X - A - B, X is on L, by definition, but off AB, also by def. but under the hypothesis L = AB, -><-"
  have ⟨X, colXAB, distinctXAB, XAB⟩ := ref lemma 1.0.5 A B AneB
  separate at distinctXAB;
  have XonL : X on L := by
    idea "L = AB, and L = colXAB.line by the ref lemma 2.0.2"
    have LeqXAB : L = colXAB.line := by
      have ABeqXAB := ref lemma 2.0.2 AneB
        ⟨(by obvious : A on ray A B), colXAB.mem A,
         (by obvious : B on ray A B), colXAB.mem B⟩
      rw [<- ABeqXAB]; exact ABeqL.symm
    rw [LeqXAB]; exact colXAB.mem X
  rw [<- ABeqL] at XonL
  rcases XonL with XonSeg | XonExt
  · rcases XonSeg with AXB | AeqX | BeqX
    · exact ref lemma 1.0.36 ⟨XAB, AXB⟩
    · exact absurd AeqX XneA.symm
    · exact absurd BeqX XneB.symm
  · have ⟨ABX, _, _⟩ := XonExt
    exact ref lemma 1.0.38 ⟨ABX, XAB⟩


atlas commentary := by
  ref lemma 2.0.13
  name "Segment Commutativity"
  preface "It helps to be able to commute these around, when we get to congruence this will make part of it trivial"

atlas lemma 2.0.13 "Segment Commutativity"
  : (segment A B : Line) = segment B A := by
  suffices subset : ∀ A B : Point, (segment A B : Line) ⊆ segment B A by
    exact Line.eq_of_subset (subset A B) (subset B A)
  intro A B P hPinSegAB
  rcases hPinSegAB with APB | AeqP | BeqP
  all_goals obvious

attribute [obvious] «Segment Commutativity»


atlas commentary := by
  ref lemma 2.0.14
  name "A segment A B is never equal to any line L"
  preface "A line is 'bigger' than a segment, in the same way that a line is bigger than a ray (2.0.12)"

atlas lemma 2.0.14 "A segment A B is never equal to any line L"
  { L : Line } {A B : Point}  (AneB : A ≠ B := by assumption) : segment A B ≠ L := by
  intro ABeqL
  have AonL : A on L := by rw [<- ABeqL]; obvious
  have BonL : B on L := by rw [<- ABeqL]; obvious
  have ⟨X, colXAB, distinctXAB, XAB⟩ := ref lemma 1.0.5 A B AneB
  separate at distinctXAB
  have XonL : X on L := by
    have LeqXAB : L = colXAB.line :=
      ref lemma 2.0.2 AneB ⟨AonL, colXAB.mem A, BonL, colXAB.mem B⟩
    rw [LeqXAB]; exact colXAB.mem X
  rw [<- ABeqL] at XonL
  rcases XonL with AXB | AeqX | BeqX
  · exact ref lemma 1.0.36 ⟨XAB, AXB⟩
  · exact absurd AeqX XneA.symm
  · exact absurd BeqX XneB.symm

attribute [obvious] «A segment A B is never equal to any line L»
                    «A ray A B is never equal to any line L»

end Line

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
  : (segment A B : Line) ∩ extension A B = ∅ := by
  apply Line.ext_set
  rw [Line.inter_toSet, Line.empty_toSet]
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
  have interEmpty : (segment A B : Line) ∩ (extension A B : Line) = ∅ := ref lemma 2.0.15
  have XinInter : X ∈ ((segment A B : Line) ∩ (extension A B : Line)) := by obvious
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
  have interEmpty : (segment A B : Line) ∩ (extension A B : Line) = ∅ := ref lemma 2.0.15
  have XinInter : X ∈ ((segment A B : Line) ∩ (extension A B : Line)) := by obvious
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
  have XeqP : X = P := by obvious
  have YeqP : Y = P := by obvious
  rw [XeqP, YeqP]


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
    apply Line.eq_of_subset
    · intro Q QinInter
      have h := ref lemma 2.0.18 L M LneM LnparM ⟨QinInter, PinInter⟩
      trivial
    · intro Q QisP
      have QeqP : Q = P := by obvious
      rw [QeqP]; exact PinInter
  · intro LintMatP
    rw [LintMatP]
    trivial


atlas commentary := by
  ref lemma 2.0.21
  name "A line intersecting a segment intersects its containing ray at the same point"
  preface "If a line intersects a segment, then it intersects the ray containing that segment"

atlas lemma 2.0.21 "A line intersecting a segment intersects its containing ray at the same point"
  : (A ≠ B) -> (L intersects segment A B at X) -> (L intersects ray A B at X) := by
  intro AneB LintABatX
  have XonSegAB : X on segment A B := ref lemma 1.0.33 LintABatX
  have XonL : X on L := ref lemma 1.0.32 LintABatX
  have LneRayAB : L ≠ (ray A B : Line) := by
    by_contra! hNeg
    rw [hNeg] at LintABatX
    have AonIntRaySeg : A ∈ ((ray A B : Line) ∩ (segment A B : Line)) := by obvious
    have BonIntRaySeg : B ∈ ((ray A B : Line) ∩ (segment A B : Line)) := by obvious
    rw [LintABatX] at AonIntRaySeg BonIntRaySeg
    have AeqB : A = B := by obvious
    contradiction
  have LnparRayAB : L ∦ ray A B := by obvious
  -- assume there is some point not X that intersects the ray.
  by_cases counter : ∃ P : Point, (L intersects ray A B at P) ∧ (P ≠ X)
  · obtain ⟨P, LintRayABatP, PneX⟩ := counter
    have XinInter : X ∈ L ∩ ray A B := by obvious
    unfold Intersects at LintRayABatP
    rw [LintRayABatP] at XinInter
    have XeqP : P = X := by obvious
    contradiction
  · push Not at counter
    apply Line.eq_of_subset
    · intro P PonLintRay
      have XonLintRay : X ∈ L ∩ ray A B := Line.mem_inter.mpr ⟨XonL, obvious⟩
      have PeqX : P = X := ref lemma 2.0.18 L (ray A B) LneRayAB LnparRayAB ⟨PonLintRay, XonLintRay⟩
      rw [PeqX]
      trivial
    · intro P PinSingleX
      have PeqX : P = X := by obvious
      rw [PeqX]; obvious


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
  have XABCol := @Line.«Ray Points are Collinear» A B X AneB XonRayAB
  have XonLineAB : X on line A B := ref lemma 1.0.18 XonRayAB
  have XonRayAB : X on ray A B := by obvious
  have XinInter : X ∈ L ∩ line A B := by obvious
  have LnparRayAB : L ∦ ray A B := ref lemma 2.0.22 LintRay
  have LnparLineAB : L ∦ line A B := by
    unfold Parallel
    push Not
    intro LneLineAB
    use X
    obvious
  have LneRayAB : L ≠ ray A B := Ne.symm (ref lemma 2.0.12)
  have LneLineAB : L ≠ line A B := by
    by_contra! hNeg
    have AonLineAB : A on line A B := by obvious
    have AonRayAB : A on ray A B := by obvious
    have AonL : A on L := by
      have h : A ∈ (line A B : Line) := AonLineAB
      rw [<- hNeg] at h; obvious
    have BonLineAB : B on line A B := by obvious
    have BonRayAB : B on ray A B := by obvious
    have BonL : B on L := by
      have h : B ∈ (line A B : Line) := BonLineAB
      rw [<- hNeg] at h; obvious
    have LintABatA : L intersects ray A B at A := (ref lemma 2.0.20 A L (ray A B : Line) ⟨LneRayAB, LnparRayAB⟩).mp obvious
    have LintABatB : L intersects ray A B at B := (ref lemma 2.0.20 B L (ray A B : Line) ⟨LneRayAB, LnparRayAB⟩).mp obvious
    unfold Intersects at *
    rw [LintRay] at LintABatA
    rw [LintRay] at LintABatB
    rw [LintABatB] at LintABatA
    simp only [Line.singleton_eq_singleton] at LintABatA
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
    apply Line.eq_of_subset
    · intro P PinInter
      exact counter P ((ref lemma 2.0.20 P L (line A B) ⟨LneLineAB, LnparLineAB⟩).mp PinInter)
    · intro P PisX
      have PeqX : P = X := by obvious
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
  have distinctAXB := (ref axiom B.1 AXB).distinct
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
  obvious



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
    obvious
  unfold Splits Guards at MsplitsAB; push Not at MsplitsAB
  specialize MsplitsAB AoffM BoffM
  obtain ⟨AneB, P, PonSeg, PonM⟩ := MsplitsAB
  have LeqAB : L = line A B := ref lemma 2.0.2 AneB ⟨AonL, obvious, BonL, obvious⟩
  have PonL : P on L := by
    apply ref lemma 2.0.5 at PonSeg
    rw [<- LeqAB] at PonSeg
    trivial
  have PeqX : P = X := by
    have PinLintM : P ∈ L ∩ M := by obvious
    rw [LintMatX] at PinLintM
    obvious
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
  have XonEX : X on (line E X) := by obvious
  have EonEX : E on (line E X) := by obvious
  have ne : L ≠ (line E X) := by
    by_contra! hNeg; rw [hNeg] at EoffL; contradiction
  have npar : L ∦ (line E X) := by
    intro hpar
    have XinInter : X ∈ L ∩ (line E X) := ⟨XonL, XonEX⟩
    have hEmpty : L ∩ (line E X) = ∅ := by obvious
    rw [hEmpty] at XinInter
    exact absurd XinInter (Set.notMem_empty X)
  have XonLintEX : X ∈ L ∩ (line E X) := by obvious
  have int : L intersects (line E X) at X := (ref lemma 2.0.20 X L (line E X) ⟨ne, npar⟩).mp XonLintEX
  obvious


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

atlas commentary := by
  ref lemma 3.0.1
  name "Bare intersection plus a shared point implies pointed intersection or coincidence"
  preface "If `L intersects M` and `A` lies on both, then either the intersection happens
at `A` specifically (`L intersects M at A`) or the two coincide."
  notes "`intersects` is the weak (\"nonempty intersection\") form, so the proof needs
`line_trichotomy` to pin down which of the three cases obtains; `A ∈ L ∩ M`
rules out the empty branch, leaving either the unique-point branch (which
must be `A`) or the coincident branch."

atlas lemma 3.0.1 "Bare intersection plus a shared point implies pointed intersection or coincidence"
  {L M : Line} {A : Point} :
    L intersects M -> A on L ∧ A on M -> L intersects M at A ∨ L = M := by
  intro _LintM ⟨AonL, AonM⟩
  have AinInt : A ∈ L ∩ M := Line.mem_inter.mpr ⟨AonL, AonM⟩
  rcases ref lemma 2.0.1 L M with empty | unique | equal
  · exfalso; rw [empty] at AinInt; exact (Line.not_mem_empty AinInt)
  · left
    obtain ⟨X, hX, _⟩ := unique
    rw [hX] at AinInt
    have AeqX : A = X := Line.mem_singleton.mp AinInt
    change L ∩ M = ({A} : Line)
    rw [hX, AeqX]
  · right; exact equal


atlas commentary := by
  ref lemma 3.0.2
  name "A line intersects itself (bare intersection of L with L)"
  preface "A line trivially intersects itself everywhere."

atlas lemma 3.0.2 "A line intersects itself (bare intersection of L with L)"
  : L intersects L := by
  obtain ⟨A, _, _, AonL, _⟩ := ref axiom I.2 L
  exact ⟨A, AonL, AonL⟩

atlas lemma 3.7.2 "If L intersects M, then there is a point at which it intersects M, WLOG X"
  {L M : Line} : L ≠ M -> L intersects M -> ∃ X : Point, L intersects M at X := by
  intro LneM LintM
  rcases ref lemma 2.0.1 L M with empty | unique | equal
  · exfalso
    obtain ⟨X, hX⟩ := LintM
    have hMem : X ∈ L ∩ M := Line.mem_inter.mpr hX
    rw [empty] at hMem; exact Line.not_mem_empty hMem
  · obtain ⟨X, hX, _⟩ := unique
    exact ⟨X, hX⟩
  · exact absurd equal LneM

atlas lemma 3.7.3 "If L splits A and B, then L intersects segment A B"
  {L : Line} {A B : Point} : (L splits A and B) -> (L intersects segment A B) := by
  intro LsplitsAB
  by_cases hA : A on L
  · exact ⟨A, hA, by obvious⟩
  by_cases hB : B on L
  · exact ⟨B, hB, by obvious⟩
  unfold Splits Guards at LsplitsAB
  push Not at LsplitsAB
  obtain ⟨_, P, PonSeg, PonL⟩ := LsplitsAB hA hB
  exact ⟨P, PonL, PonSeg⟩

atlas corollary 3.7.3 "If L guards A and B, then L does not intersect segment A B"
  {L : Line} {A B : Point} : (L guards A and B) -> ¬(L intersects segment A B) := by
  intro ⟨AoffL, BoffL, hCase⟩ ⟨X, XonL, XonSeg⟩
  rcases hCase with AeqB | hAvoids
  · subst AeqB
    rcases XonSeg with AXA | AeqX | AeqX
    · have : distinct A X A := (ref axiom B.1 AXA).distinct
      separate at this; contradiction
    · rw [<- AeqX] at XonL; exact AoffL XonL
    · rw [<- AeqX] at XonL; exact AoffL XonL
  · exact (hAvoids X XonSeg) XonL

end Intersection

/-- Dot-notation wrappers -/
@[symm] def Guards.symm {A B : Point} {L : Line} (h : Guards A B L) : Guards B A L := by obvious
@[symm] def Splits.symm {A B : Point} {L : Line} (h : Splits L A B) : Splits L B A := by obvious

end Geometry.Theory
