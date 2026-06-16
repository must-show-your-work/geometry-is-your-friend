import Geometry.Theory.Tangling
import Geometry.Theory.Interpendices.A
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

/-- Membership against the chosen Line via Tangling's Collinear witness; the
bound filter is a TODO refinement layered on later. -/
def contains (L : Line) (P : Point) : Prop := P ∈ L.tangling.col.line

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

/-- Two lines are equal if two distinct points lie on both and bounds match.
Source: lemma 2.0.2 reformulated at the LineV2 level. -/
theorem Line.ext {L M : Line}
    (h₂ : ∃ p q, L.contains p ∧ L.contains q ∧ M.contains p ∧ M.contains q ∧ p ≠ q)
    (hl : L.leftBound = M.leftBound) (hr : L.rightBound = M.rightBound) :
    L = M := by sorry

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
    P ∈ mkLine A B h ↔ P = A ∨ P = B ∨ A - P - B ∨ A - B - P ∨ P - A - B := by sorry
theorem Line.mem_ray {A B P : Point} (h : A ≠ B) :
    P ∈ mkRay A B h ↔ P = A ∨ P = B ∨ A - P - B ∨ A - B - P := by sorry
theorem Line.mem_segment {A B P : Point} (h : A ≠ B) :
    P ∈ mkSegment A B h ↔ P = A ∨ P = B ∨ A - P - B := by sorry

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
