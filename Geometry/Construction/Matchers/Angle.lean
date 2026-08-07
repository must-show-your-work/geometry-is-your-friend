/-
Geometry/Construction/Matchers/Angle.lean — `Angle A B C` gestalt matcher.

Priority 100: a composite of leaf matchers. Greenberg's `Angle A B C`
is structurally `(ray A B ≠ ray A C) ∧ ¬OppositeRay A B C`, but the
figure's intent is "A is the vertex of an angle with sides ray AB and
ray AC, and the three points are noncollinear." Translating to the
DSL: construct the two rays explicitly + assert noncollinearity.

Bottom-up walking the `∧` shape would lose the rays — they're implied
by the type-name, not present in the conjunction. This whole-type
matcher captures the gestalt.

The priority places this above the leaf matchers (priority 0) so any
`Angle` hypothesis hits this first; the `(ray A B ≠ ray A C)` and
`¬OppositeRay` conjuncts never get individually classified.
-/

import Figures.Construction.ProofState
import Geometry.Construction.Matchers.Helpers

namespace Geometry.Construction.Matchers

open Lean Meta
open Figures.Construction.DSL
open Figures.Construction.ProofState

@[proof_state_matcher 100]
def matchAngle : Matcher := fun e => do
  match (← instantiateMVars e).getAppFnArgs with
  | (`Geometry.Theory.Angle, #[a, b, c]) =>
    let some args ← readPointArgs #[a, b, c] | return none
    let #[A, B, C] := args | return none
    let rayAB := s!"ray_{A}_{B}"
    let rayAC := s!"ray_{A}_{C}"
    return some #[
      .construct rayAB (.app "ray" [.name A, .name B]),
      .construct rayAC (.app "ray" [.name A, .name C]),
      assertN "noncollinear" #[A, B, C],
    ]
  | _ => return none

end Geometry.Construction.Matchers
