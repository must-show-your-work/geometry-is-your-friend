import Geometry.Theory.Collinear
import Geometry.Theory.Arrangement
import Geometry.Theory.Arrangement.Lattice

namespace Geometry.Theory

/-- Search space over Arrangements of a set of collinear points. -/
structure Tangling where
  points : Finset Point
  col : Collinear points
  known : Finset ((a : Point) ×' (b : Point) ×' (c : Point) ×' Between a b c)

namespace Tangling

/-- A Tangling of size at least n. Methods like `.arrangements` require ≥ 3. -/
def SizeGe (t : Tangling) (n : Nat) : Prop := t.points.card ≥ n

/-- Add a known Between fact among existing points; refines the search space. -/
noncomputable def addBetween (t : Tangling) {a b c : Point}
    (_ha : a ∈ t.points) (_hb : b ∈ t.points) (_hc : c ∈ t.points)
    (h : a - b - c) : Tangling :=
  { t with known := insert ⟨a, b, c, h⟩ t.known }

/-- Add a new collinear point; expands the search space. -/
noncomputable def weaveIn (t : Tangling) (P : Point)
    (hcol : Collinear (insert P t.points)) : Tangling :=
  { points := insert P t.points, col := hcol, known := t.known }

open Geometry.Theory.Arrangement.Lattice in
/-- The linear extensions of `t`'s partial order as ordered point lists. -/
noncomputable def extensions (t : Tangling) : List (List Point) :=
  let pts := t.points.toList
  let n := pts.length
  let idx : Point → Nat := fun p => pts.idxOf p
  let edges : Array (Nat × Nat) :=
    t.known.toList.foldl (init := #[]) fun acc ⟨a, b, c, _⟩ =>
      (acc.push (idx a, idx b)).push (idx b, idx c)
  match enumLinearExtensions n edges with
  | .ok exts =>
    exts.toList.map fun ext =>
      ext.toList.filterMap fun i => pts[i]?
  | .error _ => []

/-- A Tangling is consistent if its partial order has at least one extension. -/
def Consistent (t : Tangling) : Prop := t.extensions ≠ []

/-- The number of consistent total orderings. Zero ⇒ inconsistent (cycle). One ⇒
fully untangled. Multiple ⇒ ambiguous; users dispatch via `untangle`. -/
noncomputable def ambiguity (t : Tangling) : Nat := t.extensions.length

/-- An inconsistent Tangling (zero consistent extensions) yields False — the
known Between facts form a cycle in the partial order. Used by `untangle` to
auto-close False goals when the input Tangling is contradictory. -/
theorem cycle_imp_false (t : Tangling) (h : t.extensions = []) : False := by sorry

end Tangling

/-- A 2-point Tangling — the minimal nontrivial case, no Between facts known. -/
noncomputable def Tangling.pair (A B : Point) (h : A ≠ B := by assumption) : Tangling :=
  { points := {A, B}, col := via lemma 1.0.5 h, known := ∅ }

end Geometry.Theory
