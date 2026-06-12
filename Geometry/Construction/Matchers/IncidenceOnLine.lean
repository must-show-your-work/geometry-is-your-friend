/-
Geometry/Construction/Matchers/IncidenceOnLine.lean — `P on L` and
`P off L` for fvar Lines (not LineThrough/Ray/Segment containers).

`matchOnLineThrough` (in `LineMembership.lean`) handles incidence where
the line is *constructed* via `line_through`, `ray`, or `segment`. When
the line is an existential/binder variable (e.g. `∀ L : Line, ∃ P, P
on L`), there's no constructor to extract anchors from, so a separate
matcher is needed that emits a plain `incident P L` assertion the
constraint graph then handles via existing line-anchor logic.

`P off L` mirrors `P on L` and emits the `off P L` head — handled by
`ConstraintGraph` to register `noncollinear(P, anchor0, anchor1)`.
-/

import Figures.Construction.ProofState
import Geometry.Construction.Matchers.Helpers

namespace Geometry.Construction.Matchers

open Lean Meta
open Figures.Construction.DSL
open Figures.Construction.ProofState

private def memArgs? (e : Expr) : MetaM (Option (Expr × Expr)) := do
  match (← instantiateMVars e).getAppFnArgs with
  | (``Membership.mem, args) =>
    if args.size < 5 then return none
    return some (args[4]!, args[3]!)
  | _ => return none

@[proof_state_matcher 10]
def matchOnLine : Matcher := fun e => do
  let some (elt, container) ← memArgs? e | return none
  match container.getAppFnArgs with
  | (`Geometry.Theory.Line.toSet, #[lineExpr]) =>
    let some p ← readPointName? elt | return none
    let some l ← readLineName? lineExpr | return none
    return some #[assertN "incident" #[p.toString, l.toString]]
  | _ => return none

@[proof_state_matcher 10]
def matchOffLine : Matcher := fun e => do
  match (← instantiateMVars e).getAppFnArgs with
  | (``Not, #[inner]) =>
    let some (elt, container) ← memArgs? inner | return none
    match container.getAppFnArgs with
    | (`Geometry.Theory.Line.toSet, #[lineExpr]) =>
      let some p ← readPointName? elt | return none
      let some l ← readLineName? lineExpr | return none
      return some #[assertN "off" #[p.toString, l.toString]]
    | _ => return none
  | _ => return none

end Geometry.Construction.Matchers
