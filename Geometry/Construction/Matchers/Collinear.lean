/-
Geometry/Construction/Matchers/Collinear.lean — `Collinear {…} → assert collinear …`
-/

import Figures.Construction.ProofState
import Geometry.Construction.Matchers.Helpers

namespace Geometry.Construction.Matchers

open Lean Meta
open Figures.Construction.DSL
open Figures.Construction.ProofState

@[proof_state_matcher 0]
def matchCollinear : Matcher := fun e => do
  match (← instantiateMVars e).getAppFnArgs with
  | (`Geometry.Theory.Collinear, #[s]) =>
    let some pts ← readFinsetPoints s | return none
    return some #[assertN "collinear" pts]
  | _ => return none

end Geometry.Construction.Matchers
