/-
Geometry/Construction/Matchers/OppositeRay.lean — `¬OppositeRay V X Z`.

The negation alone is technically weaker than `noncollinear` (it
allows rays-equal), but combined with `distinct` it's the geometric
content of Greenberg's angle predicate. For figures, emitting
`noncollinear` is the right intent in all real angle contexts. The
companion `matchAngle` at priority 100 fires first for `Angle V X Z`
hypotheses and supersedes this leaf matcher when both apply.

Positive `OppositeRay` (without the Not) emits no constraints — the
figure renderer has no way to express "B and C on opposite sides of A"
yet, and the points-and-line setup is captured by sibling matchers
when they coexist in the proof state.
-/

import Figures.Construction.ProofState
import Geometry.Construction.Matchers.Helpers

namespace Geometry.Construction.Matchers

open Lean Meta
open Figures.Construction.DSL
open Figures.Construction.ProofState

@[proof_state_matcher 0]
def matchNotOppositeRay : Matcher := fun e => do
  match (← instantiateMVars e).getAppFnArgs with
  | (``Not, #[inner]) =>
    match inner.getAppFnArgs with
    | (`Geometry.Theory.OppositeRay, #[v, x, z]) =>
      let some args ← readPointArgs #[v, x, z] | return none
      return some #[assertN "noncollinear" args]
    | _ => return none
  | _ => return none

end Geometry.Construction.Matchers
