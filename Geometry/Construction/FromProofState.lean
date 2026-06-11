/-
Geometry/Construction/FromProofState.lean — walk the LocalContext into
a `DSL.Construction`.

The actual Type→Stmt translation lives in `Figures.Construction.ProofState`'s
open registry of matchers (one matcher per Prop family). This file
hosts:
1. The driver: walk the LCtx, classify each non-Point local, dedup, emit.
2. A small structural fallback for `And`-conjunctions and generic `Not`
   wrapping — these don't fit "single Prop" matchers but are common
   enough to handle here. Specific Not patterns (e.g., `¬OppositeRay`)
   live as registry entries and supersede the generic Not fallback.

Domain matchers live in `Geometry/Construction/Matchers/`; the
aggregator there imports each one so its `@[proof_state_matcher]`
registration runs at module-init.
-/

import Lean
import Figures.Construction.DSL
import Figures.Construction.ProofState
import Geometry.Construction.Matchers

namespace Geometry.Construction.FromProofState

open Lean Meta
open Figures.Construction.DSL

/-- Classify a Prop-type into a list of stmts. Tries the registry
first; falls through to structural handling of `And` and generic
`Not` (each emitted stmt gets wrapped with a `¬` head). -/
partial def classify (ty : Expr) : MetaM (Array Stmt) := do
  let ty ← instantiateMVars ty
  if let some result ← Figures.Construction.ProofState.classify ty then
    return result
  match ty.getAppFnArgs with
  | (``And, #[l, r]) =>
    return (← classify l) ++ (← classify r)
  | (``Not, #[inner]) =>
    let inner ← classify inner
    return inner.map fun s => match s with
      | .assert (.app head args) _ => .assert (.app "¬" [.app head args]) ""
      | other => other
  | _ => return #[]

/-- Walk the current `LocalContext`; emit a `DSL.Construction` that
mirrors what the user could have hand-written as a `construction { … }`
block to describe the proof state. -/
def extract : MetaM Construction := do
  let lctx ← getLCtx
  let mut points : Std.HashSet String := {}
  let mut pointOrder : Array String := #[]
  let mut asserts : Array Stmt := #[]
  let mut seenStmt : Std.HashSet String := {}
  for decl in lctx do
    if decl.isImplementationDetail then continue
    let ty ← instantiateMVars decl.type
    if ty.isConstOf `Geometry.Theory.Point then
      let n := decl.userName.toString
      if !points.contains n then
        points := points.insert n
        pointOrder := pointOrder.push n
    else
      for s in (← classify ty) do
        let key := printStmt s
        if seenStmt.contains key then continue
        seenStmt := seenStmt.insert key
        asserts := asserts.push s
  let existsStmts : Array Stmt := if pointOrder.isEmpty then #[]
    else #[.«exists» pointOrder "Point"]
  return ⟨existsStmts ++ asserts⟩

end Geometry.Construction.FromProofState
