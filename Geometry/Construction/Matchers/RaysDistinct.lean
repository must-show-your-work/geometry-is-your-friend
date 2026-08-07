/-
Geometry/Construction/Matchers/RaysDistinct.lean — match `ray V X ≠
ray V Z` (rays from the same vertex are distinct) and emit both rays
as construct stmts.

This covers the case where an `Angle V X Z` hypothesis has been
destructured (e.g. `obtain ⟨dABC, _⟩ := aCAB`) so the intact Angle
matcher no longer fires, but a "rays-distinct" piece survives in LCtx.
Combined with `matchNotOppositeRay` (on the other half) this recovers
most of the original Angle gestalt's figure contribution.

Priority 50 — below the full `matchAngle` gestalt (100) so the latter
wins when the intact Angle hypothesis is present.
-/

import Figures.Construction.ProofState
import Geometry.Construction.Matchers.Helpers

namespace Geometry.Construction.Matchers

open Lean Meta
open Figures.Construction.DSL
open Figures.Construction.ProofState

/-- Walk through possible coercion wrappers to find an inner
`Geometry.Theory.Ray.from_` application; return the (vertex, endpoint)
pair if found. -/
private partial def findRayFrom (e : Expr) : Option (Expr × Expr) :=
  match e.getAppFnArgs with
  | (`Geometry.Theory.Ray.from_, #[a, b]) => some (a, b)
  | (_, args) => args.findSome? findRayFrom

@[proof_state_matcher 50]
def matchRaysDistinct : Matcher := fun e => do
  match (← instantiateMVars e).getAppFnArgs with
  | (``Ne, #[_, lhs, rhs]) =>
    let some (v1, x) := findRayFrom lhs | return none
    let some (v2, z) := findRayFrom rhs | return none
    -- Both rays must emanate from the same vertex.
    let some nv1 ← readPointName? v1 | return none
    let some nv2 ← readPointName? v2 | return none
    if nv1 != nv2 then return none
    let some nx ← readPointName? x | return none
    let some nz ← readPointName? z | return none
    let V := nv1.toString
    let X := nx.toString
    let Z := nz.toString
    return some #[
      .construct s!"ray_{V}_{X}" (.app "ray" [.name V, .name X]),
      .construct s!"ray_{V}_{Z}" (.app "ray" [.name V, .name Z]),
    ]
  | _ => return none

end Geometry.Construction.Matchers
