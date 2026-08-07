/-
Geometry/Theory/Arrangement/Lattice.lean — linear-extension enumeration
over a partial-order DAG.

`enumLinearExtensions n edges` runs Kahn's algorithm with *branching*:
at every step that has ≥ 2 in-degree-0 nodes ready, the algorithm
spawns one branch per ready node and accumulates each into the result.
Returns every valid linear order, or `.ok #[]` if the graph contains
a cycle (no extension exists). Refuses `n > maxArrangementSize` with
an explicit error so we don't silently outgrow the `CoeDep` cap.

This is pure functional Lean — no `MetaM` dependency. Consumed by the
`organize!` driver tactic in `Arrangement.lean` after the per-collinear-
group edge list has been built. Per-group ambiguity becomes a
disjunction; per-group cycle becomes a `False` proof.
-/

import Mathlib.Data.List.Basic

namespace Geometry.Theory.Arrangement.Lattice

/-- The `gen_arrangement_coes_up_to` machinery in `Arrangement.lean` caps
at 7. Stay in step: `enumLinearExtensions` refuses larger inputs. -/
def maxArrangementSize : Nat := 7

/-- Cap on the number of enumerated extensions before bailing.
Linear extensions of an n-element poset can grow up to `n!`; even at
n=7 the worst case is 5040, but the surface our proofs hit is much
smaller (≤ 6 in practice). The hard cap is a guardrail against
runaway enumeration on unexpected inputs. -/
def maxExtensions : Nat := 64

private structure State where
  remaining : Nat
  inDeg     : Array Nat
  visited   : Array Bool
  order     : Array Nat
deriving Inhabited

/-- Indices with in-degree 0 and not yet visited. -/
private def readyNodes (s : State) : Array Nat := Id.run do
  let mut out : Array Nat := #[]
  for i in [:s.inDeg.size] do
    if !s.visited[i]! ∧ s.inDeg[i]! == 0 then
      out := out.push i
  return out

/-- Advance the state by selecting node `v`: mark it visited, append to
order, decrement in-degrees of its successors. -/
private def advance (adj : Array (Array Nat)) (s : State) (v : Nat) : State :=
  let visited' := s.visited.set! v true
  let order'   := s.order.push v
  let inDeg' := (adj[v]!).foldl (init := s.inDeg) fun acc b =>
    acc.set! b (acc[b]! - 1)
  { remaining := s.remaining - 1, inDeg := inDeg', visited := visited', order := order' }

/-- DFS enumeration. Each call collects extensions reachable from `s`
into the `acc` array. -/
private partial def go (adj : Array (Array Nat))
    (s : State) (acc : Array (Array Nat)) : Array (Array Nat) := Id.run do
  if acc.size ≥ maxExtensions then return acc
  if s.remaining == 0 then return acc.push s.order
  let ready := readyNodes s
  if ready.isEmpty then return acc  -- cycle path — drop this branch
  let mut acc' := acc
  for v in ready do
    if acc'.size ≥ maxExtensions then break
    acc' := go adj (advance adj s v) acc'
  return acc'

/-- Enumerate every linear extension of the partial order on `[0, n)`
defined by `edges` (each `(a, b)` ⇒ `a` precedes `b`). Cycle ⇒
`.ok #[]`. Excessive size ⇒ `.error`. -/
def enumLinearExtensions (n : Nat) (edges : Array (Nat × Nat)) :
    Except String (Array (Array Nat)) := Id.run do
  if n > maxArrangementSize then
    return .error s!"enumLinearExtensions: n={n} exceeds cap {maxArrangementSize}"
  if n == 0 then return .ok #[#[]]
  -- Build adjacency and in-degree, dedup duplicate edges.
  let mut adj : Array (Array Nat) := Array.replicate n #[]
  let mut inDeg : Array Nat := Array.replicate n 0
  for (a, b) in edges do
    if a == b then return .error s!"enumLinearExtensions: self-loop at {a}"
    if a ≥ n ∨ b ≥ n then
      return .error s!"enumLinearExtensions: edge ({a},{b}) out of range [0,{n})"
    if !(adj[a]!).contains b then
      adj := adj.set! a ((adj[a]!).push b)
      inDeg := inDeg.set! b (inDeg[b]! + 1)
  let s₀ : State :=
    { remaining := n, inDeg, visited := Array.replicate n false, order := #[] }
  let extensions := go adj s₀ #[]
  return .ok extensions

/-! ## Tests

Inline checks so refactors that break enumeration get caught at
elaboration time. Add new cases as new shapes surface. -/

section Tests

-- `native_decide` is fine in this test section — we're checking a pure
-- functional computation. Mathlib's lint discourages it for soundness
-- reasons unrelated to this use.
set_option linter.style.nativeDecide false

/-- Single Between A-B-C ⇒ unique extension [0, 1, 2]. -/
example : enumLinearExtensions 3 #[(0, 1), (1, 2)] = .ok #[#[0, 1, 2]] := by native_decide

/-- 4-pt shared-left (P6 L104 shape): A-B-C ∧ A-B-P ⇒ two extensions
[A,B,C,P] and [A,B,P,C]. Edges: A→B, B→C (from A-B-C); A→B, B→P (from
A-B-P). Pool order: A=0, B=1, C=2, P=3. -/
example : enumLinearExtensions 4 #[(0, 1), (1, 2), (0, 1), (1, 3)]
        = .ok #[#[0, 1, 2, 3], #[0, 1, 3, 2]] := by native_decide

/-- 4-pt shared-outer (P6 L113 shape): A-B-C ∧ A-P-C ⇒ two extensions
[A,P,B,C] and [A,B,P,C]. Pool order: A=0, B=1, C=2, P=3. Edges:
A→B, B→C (from A-B-C); A→P, P→C (from A-P-C). -/
example : enumLinearExtensions 4 #[(0, 1), (1, 2), (0, 3), (3, 2)]
        = .ok #[#[0, 1, 3, 2], #[0, 3, 1, 2]] := by native_decide

/-- 4-pt strict chain A-B-C ∧ B-C-D ⇒ unique extension. -/
example : enumLinearExtensions 4 #[(0, 1), (1, 2), (1, 2), (2, 3)]
        = .ok #[#[0, 1, 2, 3]] := by native_decide

/-- Cycle ⇒ empty extension set. -/
example : enumLinearExtensions 3 #[(0, 1), (1, 2), (2, 0)] = .ok #[] := by native_decide

/-- Size cap ⇒ error. -/
example : (enumLinearExtensions 8 #[]).toOption = none := by native_decide

end Tests

end Geometry.Theory.Arrangement.Lattice
