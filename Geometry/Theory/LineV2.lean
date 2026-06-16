import Geometry.Theory.Tangling
import Geometry.Theory.Interpendices.A
import Geometry.Theory.Interpendices.B
import LeanTeX

namespace Geometry.Theory.LineV2

open Geometry.Theory

private def renderEndpointPair (diacritic : String) (a b : Lean.Expr) :
    LeanTeX.LatexPrinterM LeanTeX.LatexData := do
  let pa ← LeanTeX.latexPP a
  let pb ← LeanTeX.latexPP b
  let inner := pa.latex.1 ++ pb.latex.1
  return LeanTeX.LatexData.atomString (diacritic ++ "{" ++ inner ++ "}")

/-- A line, ray, or segment. Wraps a Tangling (search space of arrangements
on the underlying collinear point set) plus optional closed bounds. -/
structure Line where
  tangling : Tangling
  leftBound : Option Point
  rightBound : Option Point

namespace Line

/-- Bound points are members of the underlying tangling. -/
def Wf (L : Line) : Prop :=
  (∀ P, L.leftBound = some P → P ∈ L.tangling.points) ∧
  (∀ P, L.rightBound = some P → P ∈ L.tangling.points)

end Line

/-- The unbounded line through two distinct points. -/
noncomputable def mkLine (A B : Point) (h : A ≠ B := by assumption) : Line :=
  { tangling := Tangling.pair A B h, leftBound := none, rightBound := none }

/-- The ray from A through B, closed at A, unbounded past B. -/
noncomputable def mkRay (A B : Point) (h : A ≠ B := by assumption) : Line :=
  { tangling := Tangling.pair A B h, leftBound := some A, rightBound := none }

/-- The closed segment between A and B. -/
noncomputable def mkSegment (A B : Point) (h : A ≠ B := by assumption) : Line :=
  { tangling := Tangling.pair A B h, leftBound := some A, rightBound := some B }

namespace Line

/-- P is on L iff it's on the underlying full line AND inside the bounds:
not strictly to the left of leftBound (when set), not strictly to the right
of rightBound (when set). -/
def contains (L : Line) (P : Point) : Prop :=
  P ∈ L.tangling.col.line ∧
  (∀ leftP, L.leftBound = some leftP →
    ∀ otherP ∈ L.tangling.points, otherP ≠ leftP → ¬ P - leftP - otherP) ∧
  (∀ rightP, L.rightBound = some rightP →
    ∀ otherP ∈ L.tangling.points, otherP ≠ rightP → ¬ otherP - rightP - P)

instance : Membership Point Line where mem L P := L.contains P

/-- Project a LineV2.Line to the carrier Set Point. Set work escape hatch. -/
def toSet (L : Line) : Set Point := { P | L.contains P }

end Line

/-- Trichotomy classifier — every pair of lines is parallel, meets at a unique
point, or coincides. Replaces lemma 2.0.1's Or-disjunction. -/
inductive Trichotomy (L M : Line) : Type where
  | parallel    (h : ∀ P, ¬(L.contains P ∧ M.contains P)) : Trichotomy L M
  | meet (X : Point) (h : ∀ P, (L.contains P ∧ M.contains P) ↔ P = X) : Trichotomy L M
  | coincident  (h : L = M) : Trichotomy L M

/-- L and M share a unique point. -/
def Intersects (L M : Line) (X : Point) : Prop :=
  ∀ P, (L.contains P ∧ M.contains P) ↔ P = X

/-- L and M share no points. -/
def Parallel (L M : Line) : Prop := ∀ P, ¬(L.contains P ∧ M.contains P)

/-- Rays AB and AC are opposite if they're distinct but lie on the same line. -/
def OppositeRay (A B C : Point) (hb : A ≠ B := by assumption)
    (hc : A ≠ C := by assumption) : Prop :=
  mkRay A B hb ≠ mkRay A C hc ∧ mkLine A B hb = mkLine A C hc

/-- ∠ B A C — distinct, non-opposite rays from a common vertex A. -/
def Angle (A B C : Point) (hb : A ≠ B := by assumption)
    (hc : A ≠ C := by assumption) : Prop :=
  distinct A B C ∧ mkRay A B hb ≠ mkRay A C hc ∧ ¬OppositeRay A B C hb hc

/-- Two rays from the same vertex are coterminal if distinct and not opposite. -/
def Coterminal (A B C : Point) (hb : A ≠ B := by assumption)
    (hc : A ≠ C := by assumption) : Prop :=
  ¬OppositeRay A B C hb hc ∧ mkRay A B hb ≠ mkRay A C hc

/-- Trichotomy classifier instance — lemma 2.0.1's content as a structured
value. Proof body is the existing 2.0.1 chain restated; user finishes. -/
noncomputable def Line.trichotomy (L M : Line) : Trichotomy L M := by sorry

/-- Structural extensionality: equal tangling + matching bounds ⇒ equal Line.
The stronger 2.0.2-style ext (two shared distinct points ⇒ Line equal up to bounds)
isn't provable at this struct-level because the tangling carries identity beyond
just the underlying point set — different `known` sets give different Lines even
on the same underlying line. Setoid-style equality is the eventual fix. -/
theorem Line.ext {L M : Line}
    (ht : L.tangling = M.tangling)
    (hl : L.leftBound = M.leftBound) (hr : L.rightBound = M.rightBound) :
    L = M := by
  cases L; cases M
  simp_all

/-- An angle's two leg-lines are distinct — direct projection out of Angle's
def (replaces the P7-era helper that bridged Set Point via congrArg). -/
theorem Angle.line_ne {A B C : Point} {hb : A ≠ B} {hc : A ≠ C}
    (a : Angle A B C hb hc) : mkLine A B hb ≠ mkLine A C hc :=
  fun h => a.2.2 ⟨a.2.1, h⟩

/-- OppositeRay is symmetric in its B and C arguments. -/
theorem OppositeRay.symm_iff {A B C : Point} {hb : A ≠ B} {hc : A ≠ C} :
    OppositeRay A B C hb hc ↔ OppositeRay A C B hc hb :=
  ⟨fun ⟨h₁, h₂⟩ => ⟨h₁.symm, h₂.symm⟩,
   fun ⟨h₁, h₂⟩ => ⟨h₁.symm, h₂.symm⟩⟩

/-- `comparing L and M` introduces a `Trichotomy L M` hypothesis named `tri`
for case-splitting. Sugar for `have tri := Line.trichotomy L M`. -/
syntax (name := comparingTac) "comparing" term "and" term : tactic
macro_rules (kind := comparingTac)
  | `(tactic| comparing $L and $M) => `(tactic| have tri := Line.trichotomy $L $M)

@[simp] theorem mkLine_points {A B : Point} (h : A ≠ B) :
    (mkLine A B h).tangling.points = {A, B} := rfl
@[simp] theorem mkLine_leftBound {A B : Point} (h : A ≠ B) :
    (mkLine A B h).leftBound = none := rfl
@[simp] theorem mkLine_rightBound {A B : Point} (h : A ≠ B) :
    (mkLine A B h).rightBound = none := rfl

@[simp] theorem mkRay_points {A B : Point} (h : A ≠ B) :
    (mkRay A B h).tangling.points = {A, B} := rfl
@[simp] theorem mkRay_leftBound {A B : Point} (h : A ≠ B) :
    (mkRay A B h).leftBound = some A := rfl
@[simp] theorem mkRay_rightBound {A B : Point} (h : A ≠ B) :
    (mkRay A B h).rightBound = none := rfl

@[simp] theorem mkSegment_points {A B : Point} (h : A ≠ B) :
    (mkSegment A B h).tangling.points = {A, B} := rfl
@[simp] theorem mkSegment_leftBound {A B : Point} (h : A ≠ B) :
    (mkSegment A B h).leftBound = some A := rfl
@[simp] theorem mkSegment_rightBound {A B : Point} (h : A ≠ B) :
    (mkSegment A B h).rightBound = some B := rfl

@[simp] theorem Line.mem_def {L : Line} {P : Point} : P ∈ L ↔ L.contains P := Iff.rfl

theorem Line.mem_line {A B P : Point} (h : A ≠ B) :
    P ∈ mkLine A B h ↔ P = A ∨ P = B ∨ A - P - B ∨ A - B - P ∨ P - A - B := by
  show (mkLine A B h).contains P ↔ _
  unfold Line.contains
  simp only [mkLine_leftBound, mkLine_rightBound, reduceCtorEq, false_implies,
    implies_true, and_true]
  set L := (mkLine A B h).tangling.col.line
  have hOnA : A ∈ L := (mkLine A B h).tangling.col.on_line A (by simp)
  have hOnB : B ∈ L := (mkLine A B h).tangling.col.on_line B (by simp)
  have hEq : L = (↑(LineThrough.through A B) : Theory.Line) :=
    via lemma 2.0.2 h ⟨hOnA, Or.inl rfl, hOnB, Or.inr (Or.inl rfl)⟩
  rw [hEq]
  exact LineThrough.mem_coe_line.trans LineThrough.mem_def
theorem Line.mem_ray {A B P : Point} (h : A ≠ B) :
    P ∈ mkRay A B h ↔ P = A ∨ P = B ∨ A - P - B ∨ A - B - P := by
  constructor
  · rintro ⟨hOn, hLeft, _⟩
    have notPAB : ¬ P - A - B := hLeft A rfl B (by simp) h.symm
    rcases (mem_line h).mp ⟨hOn, by simp, by simp⟩ with eq | eq | btw | btw | btw
    · exact Or.inl eq
    · exact Or.inr (Or.inl eq)
    · exact Or.inr (Or.inr (Or.inl btw))
    · exact Or.inr (Or.inr (Or.inr btw))
    · exact absurd btw notPAB
  · intro hyp
    have hOn : P ∈ (mkRay A B h).tangling.col.line := by
      have := (mem_line h).mpr (hyp.imp id (·.imp id (·.imp id Or.inl)))
      exact this.1
    refine ⟨hOn, ?_, by simp⟩
    intro leftP hL otherP hOther hNe
    simp only [mkRay_leftBound, Option.some.injEq] at hL
    subst hL
    simp only [mkRay_points, Finset.mem_insert, Finset.mem_singleton] at hOther
    rcases hOther with rfl | rfl
    · exact (hNe rfl).elim
    · intro hPAB
      have d := (via axiom B.1 hPAB).distinct.card_eq
      rcases hyp with rfl | rfl | btw | btw
      · simp_all
      · simp_all
      · exact via lemma 1.0.18 ⟨btw, hPAB⟩
      · exact via lemma 1.0.20 ⟨btw, hPAB⟩
theorem Line.mem_segment {A B P : Point} (h : A ≠ B) :
    P ∈ mkSegment A B h ↔ P = A ∨ P = B ∨ A - P - B := by
  constructor
  · rintro ⟨hOn, hLeft, hRight⟩
    have notPAB : ¬ P - A - B := hLeft A rfl B (by simp) h.symm
    have notABP : ¬ A - B - P := hRight B rfl A (by simp) h
    rcases (mem_line h).mp ⟨hOn, by simp, by simp⟩ with eq | eq | btw | btw | btw
    · exact Or.inl eq
    · exact Or.inr (Or.inl eq)
    · exact Or.inr (Or.inr btw)
    · exact absurd btw notABP
    · exact absurd btw notPAB
  · intro hyp
    have hOn : P ∈ (mkSegment A B h).tangling.col.line := by
      have := (mem_line h).mpr
        (hyp.imp id (·.imp id Or.inl))
      exact this.1
    refine ⟨hOn, ?_, ?_⟩
    · intro leftP hL otherP hOther hNe hPAB
      simp only [mkSegment_leftBound, Option.some.injEq] at hL
      subst hL
      simp only [mkSegment_points, Finset.mem_insert, Finset.mem_singleton] at hOther
      rcases hOther with rfl | rfl
      · exact hNe rfl
      have d := (via axiom B.1 hPAB).distinct.card_eq
      rcases hyp with rfl | rfl | btw
      · simp_all
      · simp_all
      · exact via lemma 1.0.18 ⟨btw, hPAB⟩
    · intro rightP hR otherP hOther hNe hABP
      simp only [mkSegment_rightBound, Option.some.injEq] at hR
      subst hR
      simp only [mkSegment_points, Finset.mem_insert, Finset.mem_singleton] at hOther
      rcases hOther with rfl | rfl
      · have d := (via axiom B.1 hABP).distinct.card_eq
        rcases hyp with rfl | rfl | btw
        · have : ({P, B, P} : Finset Point) = {P, B} := by ext; simp; tauto
          rw [this, Finset.card_insert_of_notMem (by simp [h])] at d; simp at d
        · simp_all
        · exact via lemma 1.0.19 ⟨btw, hABP⟩
      · exact hNe rfl

open LeanTeX in
latex_pp_app_rules (const := Geometry.Theory.LineV2.mkSegment)
  | _, #[a, b, _] => renderEndpointPair "\\overline" a b

open LeanTeX in
latex_pp_app_rules (const := Geometry.Theory.LineV2.mkRay)
  | _, #[a, b, _] => renderEndpointPair "\\overrightarrow" a b

open LeanTeX in
latex_pp_app_rules (const := Geometry.Theory.LineV2.mkLine)
  | _, #[a, b, _] => renderEndpointPair "\\overleftrightarrow" a b

end Geometry.Theory.LineV2
