/-
Geometry/Construction/FromProofState.lean — walk LCtx + goal + theorem
type into a `DSL.Construction`.

All Type→Stmt translation goes through the open registry hosted in
`Figures.Construction.ProofState`. Both geometric matchers (Between,
Distinct, Collinear, Angle, …) and structural decompositions (And,
Iff, Not, Pi) are registered there — geometric in giyf, logical in
figures. This file just drives the LCtx walk and aggregates results
with dedup.
-/

import Lean
import Figures.Construction.DSL
import Figures.Construction.ProofState
import Figures.Construction.Matchers.Logical
import Geometry.Construction.Matchers

namespace Geometry.Construction.FromProofState

open Lean Meta
open Figures.Construction.DSL

/-- Classify any Expr (Prop or Type) via the registry. Returns `#[]`
when no matcher claims it. -/
def classify (ty : Expr) : MetaM (Array Stmt) := do
  let ty ← instantiateMVars ty
  return (← Figures.Construction.ProofState.classify ty).getD #[]

/-- Walk the current `LocalContext` (+ optionally the current goal
type + the full theorem type) and emit a `DSL.Construction` mirroring
what the user could have hand-written as a `construction { … }` block.

The figure illustrates the THEOREM, not the proof state. Three
sources contribute, all dispatched through the same registry:

- LCtx — hypotheses currently in scope.
- `goalTy` — the current main goal; picks up constraints from the
  conclusion that aren't in LCtx yet.
- `theoremTy` — the FULL theorem type with Pi binders intact; picks
  up constraints from PREMISES that have since been destructured out
  of the LCtx (e.g. an `Angle V X Z` parameter that `obtain` broke up).
  Without this, the figure loses content as the proof advances; with
  it, the figure stays stable across the whole proof body. -/
def extract (goalTy : Option Expr := none) (theoremTy : Option Expr := none) :
    MetaM Construction := do
  let lctx ← getLCtx
  let mut pointSeen : Std.HashSet String := {}
  let mut pointOrder : Array String := #[]
  let mut lineSeen : Std.HashSet String := {}
  let mut lineOrder : Array String := #[]
  let mut asserts : Array Stmt := #[]
  let mut seenStmt : Std.HashSet String := {}
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
      if !pointSeen.contains n then
        pointSeen := pointSeen.insert n
        pointOrder := pointOrder.push n
    else if ty.isConstOf `Geometry.Theory.Line then
      let n := decl.userName.toString
      if !lineSeen.contains n then
        lineSeen := lineSeen.insert n
        lineOrder := lineOrder.push n
    else
      let (a', s') := pushStmts asserts seenStmt (← classify ty)
      asserts := a'
      seenStmt := s'
  if let some g := goalTy then
    let (a', s') := pushStmts asserts seenStmt (← classify g)
    asserts := a'
    seenStmt := s'
  if let some tt := theoremTy then
    let (a', s') := pushStmts asserts seenStmt (← classify tt)
    asserts := a'
    seenStmt := s'
  let mut existsStmts : Array Stmt := #[]
  if !pointOrder.isEmpty then
    existsStmts := existsStmts.push (.«exists» pointOrder "Point")
  if !lineOrder.isEmpty then
    existsStmts := existsStmts.push (.«exists» lineOrder "Line")
  return ⟨existsStmts ++ asserts⟩

end Geometry.Construction.FromProofState
