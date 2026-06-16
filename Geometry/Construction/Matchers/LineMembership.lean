/-
Geometry/Construction/Matchers/LineMembership.lean — `D ∈ line_through B C`,
`P ∈ ray A B`, `P ∈ segment A B`.

All three match the `Membership.mem` shape with a recognized container.
Each emits the on-X assert + (for line_through) a `construct` for the
implied line anchor.
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

@[proof_state_matcher 0]
def matchOnLineThrough : Matcher := fun e => do
  let some (elt, container) ← memArgs? e | return none
  let bcArgs : Option (Expr × Expr) := match container.getAppFnArgs with
    | (`Geometry.Theory.LineThrough.through, #[b, c]) => some (b, c)
    | (`Geometry.Theory.LineV2.mkLine, args) =>
      if args.size ≥ 2 then some (args[0]!, args[1]!) else none
    | _ => none
  let some (b, c) := bcArgs | return none
  let some d ← readPointName? elt | return none
  let some nb ← readPointName? b | return none
  let some nc ← readPointName? c | return none
  let lineName := lineAnchor nb.toString nc.toString
  return some #[
    .construct lineName (.app "line_through"
      [.name nb.toString, .name nc.toString]),
    assertN "hidden" #[lineName],
    assertN "incident" #[d.toString, lineName]
  ]

@[proof_state_matcher 0]
def matchOnRay : Matcher := fun e => do
  let some (elt, container) ← memArgs? e | return none
  let abArgs : Option (Expr × Expr) := match container.getAppFnArgs with
    | (`Geometry.Theory.Ray.from_, #[a, b]) => some (a, b)
    | (`Geometry.Theory.LineV2.mkRay, args) =>
      if args.size ≥ 2 then some (args[0]!, args[1]!) else none
    | _ => none
  let some (a, b) := abArgs | return none
  let some p ← readPointName? elt | return none
  let some na ← readPointName? a | return none
  let some nb ← readPointName? b | return none
  let aStr := na.toString
  let bStr := nb.toString
  return some #[
    .construct s!"ray_{aStr}_{bStr}" (.app "ray" [.name aStr, .name bStr]),
    assertN "on_ray" #[p.toString, aStr, bStr],
  ]

@[proof_state_matcher 0]
def matchOnSegment : Matcher := fun e => do
  let some (elt, container) ← memArgs? e | return none
  let abArgs : Option (Expr × Expr) := match container.getAppFnArgs with
    | (`Geometry.Theory.Segment.between, #[a, b]) => some (a, b)
    | (`Geometry.Theory.LineV2.mkSegment, args) =>
      if args.size ≥ 2 then some (args[0]!, args[1]!) else none
    | _ => none
  let some (a, b) := abArgs | return none
  let some p ← readPointName? elt | return none
  let some na ← readPointName? a | return none
  let some nb ← readPointName? b | return none
  let aStr := na.toString
  let bStr := nb.toString
  return some #[
    .construct s!"seg_{aStr}_{bStr}" (.app "segment" [.name aStr, .name bStr]),
    assertN "on_segment" #[p.toString, aStr, bStr],
  ]

end Geometry.Construction.Matchers
