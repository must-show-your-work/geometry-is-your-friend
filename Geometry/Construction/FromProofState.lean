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

/-- Classify a *goal* type. Splits `Iff p q` into both sides (the
figure should reflect the configuration the theorem describes, and an
iff's two sides describe the same configuration). Pi binders are
ignored — those vars get introduced via `intro` and surface in the
LCtx walk. Other shapes fall through to the regular classifier (which
handles registry hits + structural And/Not). -/
partial def classifyGoal (ty : Expr) : MetaM (Array Stmt) := do
  let ty ← instantiateMVars ty
  match ty.getAppFnArgs with
  | (``Iff, #[l, r]) =>
    return (← classifyGoal l) ++ (← classifyGoal r)
  | _ => classify ty

/-- Walk the current `LocalContext` (+ optionally the current goal
type) and emit a `DSL.Construction` mirroring what the user could have
hand-written as a `construction { … }` block. The figure illustrates
the theorem, not the proof state — so passing the goal lets us pick up
constraints that aren't in scope yet but ARE in the conclusion (notably
the other half of an iff while you're proving one direction). -/
def extract (goalTy : Option Expr := none) : MetaM Construction := do
  let lctx ← getLCtx
  let mut points : Std.HashSet String := {}
  let mut pointOrder : Array String := #[]
  let mut asserts : Array Stmt := #[]
  let mut seenStmt : Std.HashSet String := {}
  -- Helper to merge a stmt batch with dedup.
  let pushStmts (asserts : Array Stmt) (seen : Std.HashSet String)
      (batch : Array Stmt) : Array Stmt × Std.HashSet String := Id.run do
    let mut a := asserts
    let mut s := seen
    for stmt in batch do
      let key := printStmt stmt
      if s.contains key then continue
      s := s.insert key
      a := a.push stmt
    return (a, s)
  for decl in lctx do
    if decl.isImplementationDetail then continue
    let ty ← instantiateMVars decl.type
    if ty.isConstOf `Geometry.Theory.Point then
      let n := decl.userName.toString
      if !points.contains n then
        points := points.insert n
        pointOrder := pointOrder.push n
    else
      let (a', s') := pushStmts asserts seenStmt (← classify ty)
      asserts := a'
      seenStmt := s'
  -- Layer the goal on top — its facts are what the theorem CLAIMS, not
  -- what's currently in scope. Iff splits via `classifyGoal`.
  if let some g := goalTy then
    let (a', s') := pushStmts asserts seenStmt (← classifyGoal g)
    asserts := a'
    seenStmt := s'
  let existsStmts : Array Stmt := if pointOrder.isEmpty then #[]
    else #[.«exists» pointOrder "Point"]
  return ⟨existsStmts ++ asserts⟩

end Geometry.Construction.FromProofState
