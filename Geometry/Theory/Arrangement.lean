import Mathlib.Data.List.Basic
import Geometry.Theory.Axioms
import Geometry.Theory.Arrangement.Lattice
import Geometry.Tactics

import Geometry.Ch3.Prop.P3
import Geometry.Ch3.Ex.Betweenness.Ex1
import Geometry.Construction.AtlasField

import Atlas
import LeanTeX

namespace Geometry.Theory

open Geometry.Ch3.Prop
open Geometry.Ch3.Ex
open Atlas

-- NOTE: This is a mostly vibed syntax for now; the underlying theory is something like "If you take the natural
-- generalization of betweenness you get ordered lists of points. If you have a bunch of betweenness conditions, there 
-- is some set of implied possible 'arrangements' of those points, and you might be able to deduce (via B-3 and 
-- other similar facts) a bunch of other betweenness conditions that can be useful."
--
-- Practically there are a bunch of problems with it right now, owing to the nature of vibecoding.
--
-- 1. It has trouble constructing the initial arrangement without a good amount of handholding and an arcane API. This
-- is mitigated presently through the `obvious` tactic which is itself a kitchen sink that needs working.
-- 2. you end up with a lot of proofs that are essentially "Here are all the possible arrangements under the current
-- Betweenness assumptions, rcases over them" which could be much more ergonomic.
-- 3. If you have a B condition like A-B-C and C-B-Q, you currently can't automatically derive `A-Q-B-C ∨ Q-A-B-C` which
-- are the two valid arrangements of those B conditions via any means I"ve tried. Nor a situation like `A-B-C, A-Q-B`
-- giving `A-Q-B-C`
--
-- All this before we get into congruity and managing that information on top of this.
--
-- The goal of this should be the following:
--
-- A tactic like 'arranging all points' which looks at the current proofstate and finds
-- 1. all points + all b conditions + all collinearity conditions (without b cons already present) + all
-- distinctness/inequality conditions
-- 2. gangs points into groups by collinearity
-- 3. for each group, creates a hypo with all valid arrangements on it. if there are multiple valid arrangments, it
-- creates a disjunction hypo that can be rcased over
--
-- a second tactic / extension of `by_exhaustion` which takes a arrangement disjunction and creates autonamed cases for
-- each. So if you have the a hypo like `h : A-B-C-D ∨ A-C-B-D` then `by_exhaustion h` gives two cases with hypos named
-- ABCD and ACBD
--
-- a tactic `arrange h into bcon` that takes an arrangement hypo and coerces it down to the relevant betweenness
-- condition. with the extension of `into <explicit condition>`. Works similar to `forgetting`. when you run it, it
-- tries to `obvious` the goal after running; this makes it ergonomic to prove linepart conditions.
--
-- that would turn P 3.6, in particular, from something like:
--
/-
      · have : A - B - C - P ∨ A - B - P - C := by sorry
        rcases this with ABCP | ABPC
        · have : A - C - P := by arrangement ABCP
          obvious
        · have : A - P - C := by arrangement ABPC
-/
-- to something like:
/-
      · arranging points A B C P with ABCP | ABPC
        · arrange ABCP into A - C - P
        · arrange ABPC into A - P - C
-/
-- alternatively, I wouldn't hate if I could do `arrange ABC + BPC into A-B-P` which delegates arrangement construction
-- to a 'sum' operation. This might requre re-axiomatizing betweeness to enumerate all the degenerate cases.
--
-- A-A-A is trivially true and the additive identity.
-- A-B-A is trivially true and implies B=A
-- A-B-C by construction gives distinct and collinear
--
-- A-B-C + X-A-B = X-A-B-C
-- A-B-C + A-X-B = A-X-B-C
-- A-B-C + B-X-C = A-B-X-C
-- A-B-C + B-C-X = A-B-C-X
--
-- any subset of three is a valid betweeness, so naturally if the inputs were proper (not trivial) then we have the
-- property that if we have an arrangement of any order >= 3, it is unique, and all other arrangements on the implied
-- line are false.
--
-- The most common contradiction in geometry is probably 'you have two incompatible total orders on those collinear
-- points, you're only allowed one.'
--
-- this kind of feels group-y? if A-B-C + X-X-X = A-B-C-X ∨ X-A-B-C; (trivially A-B-C + X-Y-X = A-B-C + X-X-X), I
-- suppose A-B-C + X-Y-Z = A-B-C-X-Y-Z ∨ X-Y-Z-A-B-C; we need common-pairs to deduce handedness generally. The
-- general A-B-C... + X-Y-Z with howevermuch overlap is some version of that, though. If there are no point in common,
-- `A + b(A, 0) = b(A,0)-A ∨ A-b(A,0)`; where b(A, n) is the betweenness condition with `n` points in 'common' with `A`,
-- an arbitrary arrangement. for b(A,1) and b(A,2), we have a whole mess of disjunctions though, we can align the two
-- other points relative to the 'anchor' point anywhere in the line. I suppose we need some higher concept to represent
-- this; probably Arrangement is a list of points derived from an internal list of betweenness conditions, and it
-- classifies the set of possible total orderings of those points subject to the betweeness laws. That way it's really
-- just narrowing down and expanding a collection of betweenness conditions and doing the latticework which is starting
-- to explain why it felt group-y. We can use each betweenness to collect stretches of totally ordered points within a
-- line by choosing an arbitrary point as the 'leftmost' point of the line and ordering each point as 'to the left' of
-- another. Each betweeness establishes two such relations. "A - B - C -> A left of B ∧ B left of C". to the left is
-- transitive. it is exclusive. A left of B ∨ B left of A ∧ ¬(A left of B ∧ B left of A).
--
-- This breaks the commutativity of betweenness, but that's okay, we're adopting an arbitrary reference point, we can
-- always re-arrange a betweenness with respect to that point, and in the case of full disjunction, we can just track
-- both sides. (A-B-C + X-Y-Z) with respect to A is exactly two betweenesses -- hmm, it's hard to find a canonical
-- ordering here, if we later get a A-X-Q condition, I think we end up in a case where we still can't break down to that
-- `left of` relation because it requires a fixed reference point.
--
-- So if we're stuck building the lattice by stiching betweennesses together. Then I think we can still rely on the
-- lattice approach, we know there is a total order (or we've found a contradiction which is better, if we can prove
-- multiple total orders with whatever set of assumptions, we've probably finished a proof somewhere). The goal is
-- really to measure how many possible ones we have, and once we're in a reasonable range we just rcases over them. I
-- don't know anything about lattice theory (yet) but on pure chutzpah I believe it seems reasonable to be able to like,
-- enumerate small ones completely, and maybe take a queue from chess and compute a magic hash for them over a small
-- range. We generate up to 7 coedep cases now, i suppose that'd be a target. There is probably something involving
-- whatever passes for primes in lattice theory to find some minimal set of betwixts (easier to type than betweenness).
-- If we assume we need overlapping betwixts for each pair of points, we'd need A-B-C, B-C-D, C-D-E, E-F-G, but in face
-- we only need A-B-C,C-D-E,E-F-G to boil it down to the two mirror cases. In generally I think you can drop one case
-- in four this way. The real win is if the resulting number of possible orderings drops to 0 upon the addition of any
-- condition, indicating a contradiction and probably end of proof.
--
-- I bet that's a thing, a geometry which drop the commutativity consequence from Between.Conseqeuences.
-- in such a geometry you can't be sure that A-B-C iff C-B-A. In this, you'd essentially treat an image and it's mirror
-- as distinct, so you do geometry in the mirror-world and real-world independently. All the theorems are the same, just
-- backwards in mirror world, but I think you lose maybe lemma 1.0.20 (it uses a CAB.symm).
--
--
-- If you have `n` total points in an arrangement, then there are n!/2 arrangements (each and its mirror paired by
-- .symm), if you know 1 betwixt for this, then you fix two relations out of the `n` you need to fully fix the set; 
-- you have to introduce the symmetry manually and map `left of` to `right of` as a commutativity portal kind of thing,
-- but you would have:
--
-- A left of B = B right of A
-- A left of B -> ¬(B left of A)
--
-- A-B-C ↔ A left of B ∧ B left of C
--
-- the .symm on A-B-C would have to propagate to the right-handed chiral option, that gets complicated quickly=


structure Arrangement (pts : List Point) : Prop where
  three_plus : pts.length ≥ 3
  ordered_triple : ∀ (i j k : Fin pts.length),
    i.val < j.val → j.val < k.val →
    Between (pts.get i) (pts.get j) (pts.get k)

macro_rules (kind := Geometry.Theory.dashChain)
  | `($a:term - $b:term - $c:term - $d:term $[- $rest:term]*) =>
      `(Arrangement [$a, $b, $c, $d, $rest,*])

theorem Arrangement.tri {pts : List Point} (arr : Arrangement pts)
    (i j k : Nat) (hi : i < pts.length) (hj : j < pts.length) (hk : k < pts.length)
    (hij : i < j) (hjk : j < k) :
    Between (pts.get ⟨i, hi⟩) (pts.get ⟨j, hj⟩) (pts.get ⟨k, hk⟩) :=
  arr.ordered_triple ⟨i, hi⟩ ⟨j, hj⟩ ⟨k, hk⟩ hij hjk

atlas commentary := by
  via lemma 1.0.21
  name "Arrangement.of_3 — a single A-B-C is a 3-arrangement"
  preface "A single A-B-C is a 3-arrangement."

  figure := by
    construction {
      exists A B C : Point
      assert distinct A B C
      assert between A B C
      construct segAC := segment A C
    }

atlas lemma 1.0.21 "Arrangement.of_3"
  {A B C : Point} (h : A - B - C) : Arrangement [A, B, C] := by
  refine ⟨by simp, ?_⟩
  intro i j k hij hjk
  rcases i with ⟨i, hi⟩
  rcases j with ⟨j, hj⟩
  rcases k with ⟨k, hk⟩
  simp only [show ([A, B, C] : List Point).length = 3 from rfl] at hi hj hk
  have hij : i < j := hij
  have hjk : j < k := hjk
  obtain ⟨rfl, rfl, rfl⟩ : i = 0 ∧ j = 1 ∧ k = 2 := by omega
  exact h

macro_rules (kind := dashChain)
  | `($a:term - $b:term - $c:term - $d:term $[- $rest:term]*) =>
    `(Arrangement [$a, $b, $c, $d, $rest,*])

/-! ## Auto-coercion from `Arrangement` to its contained `Between`s

Lean 4's `Coe` is type-driven, so it can't dispatch on a value-level "which
triple"; instead we enumerate one `Coe` instance per ordered triple per
arrangement size. Typeclass resolution then picks the right one by matching
the target Between's points against the (instance-generic) list entries.

Only `n=3` and `n=4` are wired up here — those are the sizes the project
currently needs. Add more by following the pattern below (`C(n,3)` instances
per size). The `.symm` direction isn't covered; write the Between in
arrangement order or apply `.symm` explicitly. -/

-- `CoeDep` (not `Coe`) because Coe's α-params must be fully determined by the
-- target β; here the non-triple points of the arrangement are never in the
-- Between's 3-tuple, so Coe rejects the instance ("does not provide concrete
-- values for (semi-)out-params"). CoeDep takes the specific value as a
-- typeclass arg, so α gets pinned by the value's type before β is consulted.
--
-- We can't write a SINGLE general instance for arbitrary `n`, because Lean's
-- typeclass resolver can't search over Nat indices (i, j, k) to pick which
-- triple matches the target Between. Instead, the command below generates one
-- CoeDep instance per (size, i, j, k) tuple, up to a chosen max size. The
-- `.symm` direction (reversed Between) is not generated; flip the orientation
-- via `.symm` at the call site if you need it.

open Lean Elab Command in
/-- Emit `CoeDep (Arrangement [p₀, …, p_{size-1}]) h (Between p_i p_j p_k)`
instances for every `(size, i<j<k<size)` with `3 ≤ size ≤ <n>`. -/
elab "gen_arrangement_coes_up_to " n:num : command => do
  let maxN := n.getNat
  if maxN < 3 then throwError "gen_arrangement_coes_up_to: need n ≥ 3"
  for size in [3:maxN+1] do
    let pointIds : Array Ident :=
      (Array.range size).map fun idx => mkIdent (Name.mkSimple s!"p{idx}")
    let listTerms : Array (TSyntax `term) := pointIds.map (⟨·.raw⟩)
    let listSyn ← `(term| [$listTerms,*])
    let binder ← `(Lean.Parser.Term.bracketedBinderF| { $[$pointIds]* : Point })
    for i in [:size] do
      for j in [i+1:size] do
        for k in [j+1:size] do
          let pi : TSyntax `term := ⟨pointIds[i]!.raw⟩
          let pj : TSyntax `term := ⟨pointIds[j]!.raw⟩
          let pk : TSyntax `term := ⟨pointIds[k]!.raw⟩
          let iLit := Syntax.mkNumLit (toString i)
          let jLit := Syntax.mkNumLit (toString j)
          let kLit := Syntax.mkNumLit (toString k)
          elabCommand (← `(
            instance $binder:bracketedBinder (h : Arrangement $listSyn) :
                CoeDep (Arrangement $listSyn) h (Between $pi $pj $pk) where
              coe := h.tri $iLit $jLit $kLit
                (by simp) (by simp) (by simp) (by decide) (by decide)))

-- Default covers the project's practical cap (book max 5, working cap ~7).
-- Bump if you start chaining bigger arrangements; cost scales as C(n,3) per
-- added size.
gen_arrangement_coes_up_to 7

/-- Walk a `List` literal expression and collect its element Exprs. -/
private partial def arrangementListElems (e : Lean.Expr) (acc : Array Lean.Expr) :
    Option (Array Lean.Expr) :=
  match Lean.Expr.getAppFnArgs e with
  | (``List.cons, #[_, hd, tl]) => arrangementListElems tl (acc.push hd)
  | (``List.nil, _)             => some acc
  | _                           => none

open Lean PrettyPrinter.Delaborator SubExpr in
@[app_delab Geometry.Theory.Arrangement]
def delabArrangement : Delab := do
  let e ← getExpr
  guard <| e.isAppOfArity ``Geometry.Theory.Arrangement 1
  let some elems := arrangementListElems (e.getArg! 0) #[] | failure
  -- 3-point Arrangements stay as the list form since `a - b - c` would
  -- parse as `Between`, not `Arrangement [a,b,c]`.
  guard <| elems.size ≥ 4
  let mut elemStxs : Array (TSyntax `term) := #[]
  for elem in elems do
    elemStxs := elemStxs.push (← Lean.PrettyPrinter.delab elem)
  let e0 := elemStxs[0]!
  let e1 := elemStxs[1]!
  let e2 := elemStxs[2]!
  let rest := elemStxs.extract 3 elemStxs.size
  `($e0 - $e1 - $e2 $[- $rest]*)

/-- Walk a List cons-chain, returning the literal prefix and an optional
non-literal tail. Symmetric with `listConsSpine` in `Primitives.lean`, but
inlined here because that one's `private` (file-scoped). When the tail is
`some _`, the printer renders `A - B - … - rest` instead of failing,
so partially-literal arrangements like `Arr [A, B, C, rest]` stay
readable. -/
private partial def arrangementSpine (e : Lean.Expr) (acc : Array Lean.Expr) :
    Array Lean.Expr × Option Lean.Expr :=
  match Lean.Expr.getAppFnArgs e with
  | (``List.cons, args) =>
    if args.size ≥ 3 then arrangementSpine args[2]! (acc.push args[1]!)
    else (acc, some e)
  | (``List.nil, _) => (acc, none)
  | _ => (acc, some e)

open LeanTeX in
latex_pp_app_rules (const := Geometry.Theory.Arrangement)
  | _, #[listExpr] => do
    let (elems, tail?) := arrangementSpine listExpr #[]
    if elems.isEmpty then failure
    let texs ← elems.mapM latexPP
    let tailTex? ← match tail? with
      | none => pure none
      | some t => pure (some (← latexPP t))
    let starOp := LatexData.binOp " - " .none 50
    let dotsAtom := LatexData.atomString "\\ldots"
    -- Build the chain. Single element + tail: `A - …rest`. Multiple
    -- elements: `A - B - … - rest`. No tail: same as before.
    if texs.size = 1 then
      match tailTex? with
      | none => return texs[0]!
      | some t =>
        return texs[0]!.protectRight 50 ++ starOp
            ++ dotsAtom ++ starOp ++ t.protectLeft 50
    let mut acc := texs[0]!.protectRight 50
    for k in [1:texs.size - 1] do
      acc := acc ++ starOp ++ texs[k]!.protect 50
    let lastIdx := texs.size - 1
    match tailTex? with
    | none =>
      return acc ++ starOp ++ texs[lastIdx]!.protectLeft 50
    | some t =>
      return acc ++ starOp ++ texs[lastIdx]!.protect 50
                ++ starOp ++ dotsAtom
                ++ starOp ++ t.protectLeft 50

end Geometry.Theory

namespace Geometry.Theory.Arrangement

open Lean Elab Tactic Meta

private partial def listExprToArray : Expr → Option (Array Expr) :=
  fun e => go e #[]
where
  go (e : Expr) (acc : Array Expr) : Option (Array Expr) :=
    match e.getAppFnArgs with
    | (``List.cons, #[_, hd, tl]) => go tl (acc.push hd)
    | (``List.nil, _)             => some acc
    | _                           => none

private def findIndex (pts : Array Expr) (target : Expr) : MetaM (Option Nat) := do
  for h : i in [:pts.size] do
    if ← isDefEq pts[i] target then
      return some i
  return none

syntax (name := arrangementTac) "arrangement" term : tactic

@[tactic arrangementTac]
def elabArrangementTac : Tactic := fun stx => match stx with
  | `(tactic| arrangement $h:term) => do
    let goal ← getMainGoal
    goal.withContext do
      let target ← instantiateMVars (← goal.getType)
      let some (x, y, z) := target.app3? ``Between
        | throwError "arrangement: goal is not of the form 'X - Y - Z'"
      let hExpr ← Term.elabTerm h none
      let hType ← instantiateMVars (← inferType hExpr)
      let some ptsExpr := hType.app1? ``Geometry.Theory.Arrangement
        | throwError "arrangement: hypothesis is not an `Arrangement`"
      let some pts := listExprToArray ptsExpr
        | throwError "arrangement: arrangement's point list is not a literal list"
      let some i ← findIndex pts x
        | throwError m!"arrangement: cannot find {x} in the arrangement"
      let some j ← findIndex pts y
        | throwError m!"arrangement: cannot find {y} in the arrangement"
      let some k ← findIndex pts z
        | throwError m!"arrangement: cannot find {z} in the arrangement"
      let iLit := Syntax.mkNumLit (toString i)
      let jLit := Syntax.mkNumLit (toString j)
      let kLit := Syntax.mkNumLit (toString k)
      if i < j && j < k then
        let tac ← `(tactic|
          exact ($h).ordered_triple
            ⟨$iLit, by simp⟩ ⟨$jLit, by simp⟩ ⟨$kLit, by simp⟩
            (by simp) (by simp))
        evalTactic tac
      else if k < j && j < i then
        let tac ← `(tactic|
          exact (($h).ordered_triple
            ⟨$kLit, by simp⟩ ⟨$jLit, by simp⟩ ⟨$iLit, by simp⟩
            (by simp) (by simp)).symm)
        evalTactic tac
      else
        throwError m!"arrangement: points are not in monotonic order \
          (indices {i}, {j}, {k}). Both X-Y-Z and Z-Y-X are supported; \
          any other interleaving needs to be derived manually."
  | _ => throwUnsupportedSyntax

/-- Parsed shape of a hypothesis passed to `organize`. -/
inductive ArrFact where
  | bet (proof : Expr) (a b c : Expr) : ArrFact
  | arr (proof : Expr) (pts : Array Expr) : ArrFact
deriving Inhabited

def ArrFact.proof : ArrFact → Expr
  | .bet p _ _ _ => p
  | .arr p _     => p

def ArrFact.points : ArrFact → Array Expr
  | .bet _ a b c => #[a, b, c]
  | .arr _ ps    => ps

private def parseArrFact (e : Expr) : MetaM (Option ArrFact) := do
  let t ← instantiateMVars (← inferType e)
  let t ← whnf t
  if let some (a, b, c) := t.app3? ``Geometry.Theory.Between then
    return some (.bet e a b c)
  if t.isAppOfArity ``Geometry.Theory.Arrangement 1 then
    let ptsExpr := t.getArg! 0
    match listExprToArray ptsExpr with
    | some pts => return some (.arr e pts)
    | none     => return none
  return none

private def addPoint (pool : Array Expr) (p : Expr) : MetaM (Nat × Array Expr) := do
  for h : i in [:pool.size] do
    if ← isDefEq pool[i] p then
      return (i, pool)
  return (pool.size, pool.push p)

/-- Kahn-style topological sort with strict uniqueness: at every step
exactly one node must have in-degree 0. Returns the topo order, an
ambiguity error, or a cycle error. -/
private def topoSort (n : Nat) (edges : Array (Nat × Nat)) :
    Except String (Array Nat) := Id.run do
  let mut adj : Array (Array Nat) := Array.replicate n #[]
  for (a, b) in edges do
    if !(adj[a]!).contains b then
      adj := adj.set! a ((adj[a]!).push b)
  let mut inDeg : Array Nat := Array.replicate n 0
  for i in [:n] do
    for b in adj[i]! do
      inDeg := inDeg.set! b (inDeg[b]! + 1)
  let mut order : Array Nat := #[]
  let mut visited : Array Bool := Array.replicate n false
  while order.size < n do
    let mut zeros : Array Nat := #[]
    for i in [:n] do
      if !visited[i]! && inDeg[i]! == 0 then
        zeros := zeros.push i
    if zeros.isEmpty then
      return .error "cycle in betweenness constraints"
    if zeros.size > 1 then
      return .error s!"ambiguous arrangement (multiple topological roots: {zeros})"
    let v := zeros[0]!
    visited := visited.set! v true
    order := order.push v
    for b in adj[v]! do
      inDeg := inDeg.set! b (inDeg[b]! - 1)
  return .ok order

private def lookupAtlasConst (kind number : String) : MetaM Name := do
  let env ← getEnv
  match Atlas.atlasLookupByNumber env kind number with
  | [n] => return n
  | []  => throwError "organize: no atlas {kind} `{number}` in scope"
  | ns  => throwError "organize: ambiguous atlas {kind} `{number}` ({ns})"

/-- For a 4-point topo order, classify which sufficient-pair lemma fits
the given pair of Between facts (in rank-triple form). Returns the
`(kind, number, idxOfH₁, idxOfH₂)` to apply, or `none`. -/
private def detect4PtPair (r0 r1 : Array Nat) : Option (String × String × Nat × Nat) :=
  let t0 := (r0[0]?.getD 0, r0[1]?.getD 0, r0[2]?.getD 0)
  let t1 := (r1[0]?.getD 0, r1[1]?.getD 0, r1[2]?.getD 0)
  -- 3.0.8 :  A-B-C  +  B-C-D   →  Arr[A,B,C,D]     (ranks (0,1,2)+(1,2,3))
  -- 3.0.9 :  A-B-D  +  B-C-D   →  Arr[A,B,C,D]     (ranks (0,1,3)+(1,2,3))
  -- alt-3.3: A-B-C  +  A-C-D   →  Arr[A,B,C,D]     (ranks (0,1,2)+(0,2,3))
  if t0 == (0,1,2) && t1 == (1,2,3) then some ("lemma", "3.0.8", 0, 1)
  else if t0 == (1,2,3) && t1 == (0,1,2) then some ("lemma", "3.0.8", 1, 0)
  else if t0 == (0,1,3) && t1 == (1,2,3) then some ("lemma", "3.0.9", 0, 1)
  else if t0 == (1,2,3) && t1 == (0,1,3) then some ("lemma", "3.0.9", 1, 0)
  else if t0 == (0,1,2) && t1 == (0,2,3) then some ("alternate", "3.3", 0, 1)
  else if t0 == (0,2,3) && t1 == (0,1,2) then some ("alternate", "3.3", 1, 0)
  else none

/-- Build a proof of `Arrangement [pool[order[0]], …, pool[order[n-1]]]`
from the available facts. Supports n=3 (single Between) and n=4
(sufficient-pair). For larger or unsupported configurations, throws. -/
private def buildArrangement
    (facts : Array ArrFact) (factRanks : Array (Array Nat))
    (n : Nat) : MetaM Expr := do
  -- Short-circuit: any input that's already the right Arrangement.
  for h : i in [:facts.size] do
    if let .arr p ps := facts[i] then
      if ps.size == n then
        let r := factRanks[i]!
        let mut isIdentity := true
        for h : k in [:n] do
          if r[k]! != k then isIdentity := false
        if isIdentity then return p
  match n with
  | 0 | 1 | 2 => throwError "organize: need at least 3 distinct points (got {n})"
  | 3 =>
    for h : i in [:facts.size] do
      if let .bet _ _ _ _ := facts[i] then
        let r := factRanks[i]!
        if r.size == 3 && r[0]! == 0 && r[1]! == 1 && r[2]! == 2 then
          let lem ← lookupAtlasConst "lemma" "1.0.21"
          return ← Meta.mkAppM lem #[facts[i].proof]
    throwError "organize: 3 points but no Between covering them in order"
  | 4 =>
    if facts.size < 2 then
      throwError "organize: 4 points but fewer than 2 Between facts"
    -- Try every pair of facts; pick the first that classifies as a sufficient pair.
    for h : i in [:facts.size] do
      for h : j in [:facts.size] do
        if i == j then continue
        let .bet _ _ _ _ := facts[i] | continue
        let .bet _ _ _ _ := facts[j] | continue
        match detect4PtPair factRanks[i]! factRanks[j]! with
        | none => pure ()
        | some (k, num, idx1, idx2) =>
          let p1 := if idx1 == 0 then facts[i].proof else facts[j].proof
          let p2 := if idx2 == 0 then facts[i].proof else facts[j].proof
          let lem ← lookupAtlasConst k num
          return ← Meta.mkAppM lem #[p1, p2]
    throwError "organize: 4 points but no recognised sufficient-pair configuration"
  | _ => throwError "organize: arrangements of size > 4 not yet supported"

syntax (name := organizeTac) "organize" (ppSpace colGt term:max)+ : tactic

/-- Detect whether the goal is the canonical inner-pair trichotomy disjunction
`(A - P - B) ∨ (P = B) ∨ (B - P - C)` and, if so, dispatch via lemma 3.0.10
using the matching inputs `A - B - C` and `A - P - C`. Returns `true` if the
case was handled. -/
private def tryTrichotomy (goal : MVarId) (facts : Array ArrFact) : MetaM Bool := do
  let goalType ← instantiateMVars (← goal.getType)
  let goalType ← whnf goalType
  unless goalType.isAppOfArity ``Or 2 do return false
  let g1 := goalType.getArg! 0
  let g23 := goalType.getArg! 1
  unless g23.isAppOfArity ``Or 2 do return false
  let g2 := g23.getArg! 0
  let g3 := g23.getArg! 1
  unless g1.isAppOfArity ``Geometry.Theory.Between 3 do return false
  unless g2.isAppOfArity ``Eq 3 do return false
  unless g3.isAppOfArity ``Geometry.Theory.Between 3 do return false
  let A := g1.getArg! 0
  let P := g1.getArg! 1
  let B := g1.getArg! 2
  let eqLhs := g2.getArg! 1
  let eqRhs := g2.getArg! 2
  let B' := g3.getArg! 0
  let P' := g3.getArg! 1
  let C := g3.getArg! 2
  unless ← isDefEq P P' do return false
  unless ← isDefEq B B' do return false
  unless ← isDefEq eqLhs P do return false
  unless ← isDefEq eqRhs B do return false
  -- Find input facts matching `A - B - C` and `A - P - C`.
  let mut hABC : Option Expr := none
  let mut hAPC : Option Expr := none
  for f in facts do
    match f with
    | .bet pr a b c =>
      if (← isDefEq a A) && (← isDefEq c C) then
        if ← isDefEq b B then hABC := some pr
        if ← isDefEq b P then hAPC := some pr
    | _ => pure ()
  match hABC, hAPC with
  | some h1, some h2 =>
    let lem ← lookupAtlasConst "lemma" "3.0.10"
    let proof ← Meta.mkAppM lem #[h1, h2]
    goal.assign proof
    return true
  | _, _ => return false

/-- Derive a `A-B-C`-style name from three point Exprs by concatenating their
user-facing names (when each is an `FVar`). Used by the reduce-not-close path
to name extracted Between hypotheses in a way the user can refer to. -/
private def betweenName (a b c : Expr) : MetaM Name := do
  let nm (e : Expr) : MetaM String := do
    match e with
    | .fvar fid => return (← fid.getUserName).toString
    | _         => return "_"
  let na ← nm a
  let nb ← nm b
  let nc ← nm c
  return Name.mkSimple (na ++ nb ++ nc)

/-- Shared core: run the organize pipeline on a given fact array and goal.
Both `organize <hyps>` (explicit hyps) and `organize_auto` (context-scan) share
this body. -/
def runOrganize (facts : Array ArrFact) (goal : MVarId) : TacticM Unit := do
  goal.withContext do
    if facts.isEmpty then
      throwError "organize: requires at least one Between or Arrangement"
    -- Disjunctive 3-way trichotomy dispatch.
    if ← tryTrichotomy goal facts then return
    -- Pool all distinct points; compute per-fact index lists.
    let mut pool : Array Expr := #[]
    let mut perFactIdx : Array (Array Nat) := #[]
    for f in facts do
      let mut idxs : Array Nat := #[]
      for p in f.points do
        let (k, newPool) ← addPoint pool p
        pool := newPool
        idxs := idxs.push k
      perFactIdx := perFactIdx.push idxs
    let n := pool.size
    -- Build edges from each fact's consecutive points.
    let mut edges : Array (Nat × Nat) := #[]
    for idxs in perFactIdx do
      for i in [:idxs.size - 1] do
        edges := edges.push (idxs[i]!, idxs[i+1]!)
    -- Topo-sort the pool indices.
    let order ← match topoSort n edges with
      | .ok o      => pure o
      | .error msg => throwError m!"organize: {msg}"
    -- rank[pool-idx] = position in topo order.
    let mut rank : Array Nat := Array.replicate n 0
    for k in [:n] do
      rank := rank.set! order[k]! k
    let factRanks : Array (Array Nat) := perFactIdx.map (·.map (rank[·]!))
    -- Build the maximal arrangement proof.
    let arrProof ← buildArrangement facts factRanks n
    -- Inspect the goal.
    let goalType ← instantiateMVars (← goal.getType)
    let goalType ← whnf goalType
    if let some (gx, gy, gz) := goalType.app3? ``Geometry.Theory.Between then
      let some ix ← findIndex pool gx
        | throwError m!"organize: goal point {gx} not in hypotheses"
      let some iy ← findIndex pool gy
        | throwError m!"organize: goal point {gy} not in hypotheses"
      let some iz ← findIndex pool gz
        | throwError m!"organize: goal point {gz} not in hypotheses"
      let rx := rank[ix]!
      let ry := rank[iy]!
      let rz := rank[iz]!
      let (i0, i1, i2, reverse) ←
        if rx < ry && ry < rz then pure (rx, ry, rz, false)
        else if rx > ry && ry > rz then pure (rz, ry, rx, true)
        else throwError m!"organize: goal points are not in arrangement order \
                                (ranks {rx}, {ry}, {rz})"
      let arrType ← Meta.inferType arrProof
      let g' ← goal.assert `arr_aux arrType arrProof
      let (_, g') ← g'.intro1P
      replaceMainGoal [g']
      g'.withContext do
        let arrIdent := mkIdent `arr_aux
        let i0Lit := Syntax.mkNumLit (toString i0)
        let i1Lit := Syntax.mkNumLit (toString i1)
        let i2Lit := Syntax.mkNumLit (toString i2)
        let body ← `(($arrIdent).tri $i0Lit $i1Lit $i2Lit
          (by simp) (by simp) (by simp) (by decide) (by decide))
        let finalTerm : TSyntax `term ←
          if reverse then `(($body).symm) else pure body
        evalTactic (← `(tactic| exact $finalTerm))
    else if goalType.isAppOfArity ``Geometry.Theory.Arrangement 1 then
      let ptsExpr := goalType.getArg! 0
      let some _ := listExprToArray ptsExpr
        | throwError "organize: goal Arrangement has non-literal point list"
      let arrType ← Meta.inferType arrProof
      if ← isDefEq arrType goalType then
        goal.assign arrProof
      else
        throwError m!"organize: built arrangement does not match goal\n  built : {arrType}\n  goal  : {goalType}"
    else
      -- Reduce-not-close: bind the arrangement AND extract every i<j<k
      -- Between as a named have (`<name>` derived from the three point
      -- identifiers, e.g. `APB`), so downstream tactics like `obvious` can
      -- consume the derived facts via simp on Between.
      let arrType ← Meta.inferType arrProof
      let g' ← goal.assert `arr_aux arrType arrProof
      let (_, g') ← g'.intro1P
      replaceMainGoal [g']
      g'.withContext do
        let arrIdent := mkIdent `arr_aux
        for i in [:n] do
          for j in [i+1:n] do
            for k in [j+1:n] do
              let iLit := Syntax.mkNumLit (toString i)
              let jLit := Syntax.mkNumLit (toString j)
              let kLit := Syntax.mkNumLit (toString k)
              let triName ← betweenName
                pool[order[i]!]! pool[order[j]!]! pool[order[k]!]!
              let nameIdent := mkIdent triName
              evalTactic (← `(tactic|
                have $nameIdent : _ := ($arrIdent).tri $iLit $jLit $kLit
                  (by simp) (by simp) (by simp) (by decide) (by decide)))

@[tactic organizeTac]
def elabOrganize : Tactic := fun stx => match stx with
  | `(tactic| organize $hs*) => do
    let goal ← getMainGoal
    goal.withContext do
      let mut facts : Array ArrFact := #[]
      for h in hs do
        let hExpr ← Term.elabTerm h none
        Term.synthesizeSyntheticMVarsNoPostponing
        let some f ← parseArrFact hExpr
          | throwError m!"organize: cannot parse `{h}` as Between or Arrangement"
        facts := facts.push f
      runOrganize facts goal
  | _ => throwUnsupportedSyntax

/-- `organize_auto`: same pipeline as `organize`, but discovers
Between/Arrangement hypotheses from the local context instead of taking
them as explicit arguments. Useful as the per-branch closer in
`arranging`. -/
syntax (name := organizeAutoTac) "organize_auto" : tactic

@[tactic organizeAutoTac]
def elabOrganizeAuto : Tactic := fun stx => match stx with
  | `(tactic| organize_auto) => do
    let goal ← getMainGoal
    goal.withContext do
      let lctx ← getLCtx
      let mut facts : Array ArrFact := #[]
      for decl in lctx do
        if decl.isImplementationDetail then continue
        if let some f ← parseArrFact decl.toExpr then
          facts := facts.push f
      runOrganize facts goal
  | _ => throwUnsupportedSyntax

/-- Detect a pair of Between facts of the form `(A-B-C, A-P-C)` — shared
outer pair `(A, C)` with different middle points — and apply lemma 3.0.10
to derive the trichotomy `(A-P-B) ∨ (P=B) ∨ (B-P-C)`. Returns the proof
expr or `none` if no such pair exists. -/
private def tryFactsTrichotomy (facts : Array ArrFact) : MetaM (Option Expr) := do
  for h : i in [:facts.size] do
    for h : j in [:facts.size] do
      if i == j then continue
      match facts[i], facts[j] with
      | .bet h1 a1 b1 c1, .bet h2 a2 _ c2 =>
        if (← isDefEq a1 a2) && (← isDefEq c1 c2) then
          -- Distinct middles ensure the trichotomy isn't vacuous. We don't
          -- check that here; if they're defeq the case-split is still sound
          -- (one branch becomes `B = B`, instantly closed).
          let lem ← lookupAtlasConst "lemma" "3.0.10"
          let proof ← Meta.mkAppM lem #[h1, h2]
          -- Only commit if mkAppM's unification was consistent with the
          -- {A, B, P, C} interpretation (i.e. the Between args of facts[i]
          -- played the role of `(A, B, C)` and facts[j] of `(A, P, C)`).
          let _ := b1
          return some proof
      | _, _ => pure ()
  return none

/-- Generate the auto-pattern for a freshly-introduced trichotomy
`(A-P-B) ∨ (P=B) ∨ (B-P-C)`. Names follow the convention `A-B-C ↦ ABC`
and `A=B ↦ AeqB`. -/
private def trichotomyAutoPattern (triType : Expr) :
    MetaM (TSyntax `Lean.Parser.Tactic.rcasesPatLo) := do
  let triType ← whnf triType
  unless triType.isAppOfArity ``Or 2 do
    throwError "arranging: trichotomy auto-pattern expected outer Or"
  let d1 := triType.getArg! 0
  let d23 := triType.getArg! 1
  let d23 ← whnf d23
  unless d23.isAppOfArity ``Or 2 do
    throwError "arranging: trichotomy auto-pattern expected inner Or"
  let d2 := d23.getArg! 0
  let d3 := d23.getArg! 1
  let nm (e : Expr) : MetaM String := do
    match e with
    | .fvar fid => return (← fid.getUserName).toString
    | _         => return "_"
  let i1 := mkIdent <| Name.mkSimple
    s!"{← nm (d1.getArg! 0)}{← nm (d1.getArg! 1)}{← nm (d1.getArg! 2)}"
  let i2 := mkIdent <| Name.mkSimple
    s!"{← nm (d2.getArg! 1)}eq{← nm (d2.getArg! 2)}"
  let i3 := mkIdent <| Name.mkSimple
    s!"{← nm (d3.getArg! 0)}{← nm (d3.getArg! 1)}{← nm (d3.getArg! 2)}"
  let p1 : TSyntax `rcasesPat ← `(rcasesPat| $i1:ident)
  let p2 : TSyntax `rcasesPat ← `(rcasesPat| $i2:ident)
  let p3 : TSyntax `rcasesPat ← `(rcasesPat| $i3:ident)
  let ps : TSyntaxArray `rcasesPat := #[p1, p2, p3]
  `(Lean.Parser.Tactic.rcasesPatLo| $ps:rcasesPat|*)

/-- `arranging <hyps>* [into <rcases-pattern>]` — case-analysis closer that
surfaces only non-obvious subgoals.

Categorizes each `<hyp>` by type:
- Between / Arrangement → "fact" (stays in scope, fed to `organize_auto`).
- anything else (Or / segment membership / etc.) → "branch" (subject to rcases).

If the inputs are all facts that share an outer pair (the canonical inner-pair
shape for lemma 3.0.10), `arranging` calls `tryFactsTrichotomy` to introduce
the trichotomy disjunction as `tri_aux` and rcases on it — using
`trichotomyAutoPattern` to name the disjuncts when no `into` is supplied.

The per-branch closer is `first | obvious | (organize_auto; obvious)`:
obvious handles trivial branches; otherwise organize_auto discovers in-scope
Between/Arrangement hyps and either dispatches the goal or extracts every
i<j<k Between from the maximal arrangement (reduce-not-close), and obvious
finishes.

### Current limits of this skeleton

1. **Single branch hyp.** Multi-branch input is rejected. Generalization
   needs a loop over `rcases b₁, b₂, … with …` and per-target pattern
   slots.
2. **No auto-pattern for branch-hyp shape.** When the branch hyp is a
   general Or-tree (e.g. the segment-union case at P5 L110), `into` is
   required. Only the trichotomy-derived shape has an auto-pattern.
   Generalising needs an Or-tree walker that emits `(…) | (…)` with
   parens on nested Ors and deduplicates leaf names (`AeqP` twice →
   `AeqP`, `AeqP_2`, …).
3. **Single rcases target.** `into` accepts one `rcasesPatLo`;
   comma-separated multi-target rcases (`rcases a, b with …`) isn't
   threaded through.
4. **Narrow ambiguity detection.** `tryFactsTrichotomy` looks for exactly
   the lemma-3.0.10 shape (two Betweens sharing the outer pair). Other
   ambiguous configurations (e.g. three Betweens with one cyclic edge,
   five-point ambiguities) silently fall through to the plain closer
   and end up at organize_auto's "ambiguous arrangement" error instead
   of being case-split. -/
syntax (name := arrangingTac) "arranging" (ppSpace colGt term:max)+
    (" into " Lean.Parser.Tactic.rcasesPatLo)? : tactic

@[tactic arrangingTac]
def elabArranging : Tactic := fun stx => match stx with
  | `(tactic| arranging $hs* $[into $pat?]?) => do
    -- FIXME: This should consider all betweenness hypos + their symmetric counterparts. Something like "Find all the
    -- betweeness hypos and construct all valid arrangements from them / their symms. The list of valid arrangements is
    -- a hypo upon which we can rcases over
    let goal ← getMainGoal
    goal.withContext do
      let mut facts : Array ArrFact := #[]
      let mut branchHyps : Array (TSyntax `term) := #[]
      for h in hs do
        let hExpr ← Term.elabTerm h none
        Term.synthesizeSyntheticMVarsNoPostponing
        if let some f ← parseArrFact hExpr then
          facts := facts.push f
        else
          branchHyps := branchHyps.push h
      let closer : TSyntax `tactic ← `(tactic|
        first
          | obvious
          | (organize_auto; obvious))
      -- If the user gave only fact hypos, see if those facts derive a
      -- trichotomy we can case-split on.
      if branchHyps.isEmpty then
        if let some triProof ← tryFactsTrichotomy facts then
          let triType ← Meta.inferType triProof
          let g' ← goal.assert `tri_aux triType triProof
          let (hFVarId, g') ← g'.intro1P
          replaceMainGoal [g']
          g'.withContext do
            let hIdent := mkIdent (← hFVarId.getUserName)
            let tgt ← `(Lean.Parser.Tactic.elimTarget| $hIdent:ident)
            let usePat ← match pat? with
              | some p => pure p
              | none   => trichotomyAutoPattern triType
            evalTactic (← `(tactic| rcases $tgt with $usePat <;> $closer))
          return
        else
          evalTactic closer
          return
      match branchHyps.size, pat? with
      | 1, some p =>
        let b := branchHyps[0]!
        let tgt ← `(Lean.Parser.Tactic.elimTarget| $b:term)
        evalTactic (← `(tactic| rcases $tgt with $p <;> $closer))
      | 1, none =>
        throwError "arranging: branch hyp requires `into <rcases-pattern>` \
                    (auto-pattern from branch shape not yet implemented)"
      | _, _ =>
        throwError "arranging: multiple branch hypotheses not yet supported"
  | _ => throwUnsupportedSyntax

/-! ## `organize!` lattice driver

Sweeps the provided Between facts (plus any `_ ≠ _` proofs needed by
split lemmas), computes all valid linear extensions of the induced
partial order on the points, and introduces the result as a single
`Arrangement` hypothesis (unique extension), a disjunction of
`Arrangement`s (multiple extensions), or — in future — derives False
(cycle).

Currently supports:
- Unique-extension case (any `n ≤ 7` covered by `buildArrangement`).
- 4-point 2-extension case via lemmas 3.0.11 (shared-left) / 3.0.12
  (shared-outer).

Other configurations error explicitly; a recursive general builder
covering them is a follow-up phase. -/

/-- userName of a Point fvar, or `?` placeholder. -/
private def pointName (e : Expr) : MetaM String := do
  match e with
  | .fvar fid => return (← fid.getUserName).toString
  | _         => return "?"

/-- Auto-name `arr<root><sink>` — root = alphabetically-first
in-degree-0 node, sink = alphabetically-first out-degree-0 node.
Falls back to `arr` if either is empty (shouldn't happen for valid
input). -/
private def computeArrName (pool : Array Expr) (edges : Array (Nat × Nat)) :
    MetaM String := do
  let n := pool.size
  let mut inDeg : Array Nat := Array.replicate n 0
  let mut outDeg : Array Nat := Array.replicate n 0
  let mut seenEdges : Array (Nat × Nat) := #[]
  for e in edges do
    if !seenEdges.contains e then
      seenEdges := seenEdges.push e
      outDeg := outDeg.set! e.1 (outDeg[e.1]! + 1)
      inDeg := inDeg.set! e.2 (inDeg[e.2]! + 1)
  let mut rootNames : Array String := #[]
  let mut sinkNames : Array String := #[]
  for i in [:n] do
    if inDeg[i]! == 0 then rootNames := rootNames.push (← pointName pool[i]!)
    if outDeg[i]! == 0 then sinkNames := sinkNames.push (← pointName pool[i]!)
  if rootNames.isEmpty ∨ sinkNames.isEmpty then return "arr"
  let rootName := (rootNames.qsort (· < ·))[0]!
  let sinkName := (sinkNames.qsort (· < ·))[0]!
  return s!"arr{rootName}{sinkName}"

/-- Find `a ≠ b` in `ineqs`, applying `.symm` if needed. -/
private def findIneq (ineqs : Array Expr) (a b : Expr) : MetaM (Option Expr) := do
  for ineq in ineqs do
    let ineqTy ← inferType ineq
    match ineqTy.getAppFnArgs with
    | (``Ne, #[_, x, y]) =>
      if (← isDefEq x a) ∧ (← isDefEq y b) then return some ineq
      if (← isDefEq x b) ∧ (← isDefEq y a) then
        return some (← mkAppM ``Ne.symm #[ineq])
    | _ => pure ()
  return none

/-- 4-point 2-extension dispatch — detect shared-left or shared-outer
configuration and apply lemma 3.0.11 or 3.0.12. -/
private def dispatch4PtSplit (pool : Array Expr) (perFactIdx : Array (Array Nat))
    (facts : Array ArrFact) (ineqs : Array Expr) : MetaM Expr := do
  unless facts.size == 2 do
    throwError "organize!: 4-pt split expects exactly 2 Betweens"
  let .bet h1 _ _ _ := facts[0]!
    | throwError "organize!: 4-pt split requires Betweens (got Arrangement)"
  let .bet h2 _ _ _ := facts[1]!
    | throwError "organize!: 4-pt split requires Betweens (got Arrangement)"
  let idx1 := perFactIdx[0]!
  let idx2 := perFactIdx[1]!
  let (a1, b1, c1) := (idx1[0]!, idx1[1]!, idx1[2]!)
  let (a2, b2, c2) := (idx2[0]!, idx2[1]!, idx2[2]!)
  if a1 == a2 ∧ b1 == b2 then
    -- Shared-LEFT: 3.0.11 (A-B-C, A-B-P, C ≠ P).
    let cExpr := pool[c1]!
    let pExpr := pool[c2]!
    let some cNeP ← findIneq ineqs cExpr pExpr
      | throwError m!"organize!: shared-left split needs `{cExpr} ≠ {pExpr}`"
    let lem ← lookupAtlasConst "lemma" "3.0.11"
    mkAppM lem #[h1, h2, cNeP]
  else if a1 == a2 ∧ c1 == c2 then
    -- Shared-OUTER: 3.0.12 (A-B-C, A-P-C, P ≠ B).
    let bExpr := pool[b1]!
    let pExpr := pool[b2]!
    let some pNeB ← findIneq ineqs pExpr bExpr
      | throwError m!"organize!: shared-outer split needs `{pExpr} ≠ {bExpr}`"
    let lem ← lookupAtlasConst "lemma" "3.0.12"
    mkAppM lem #[h1, h2, pNeB]
  else
    throwError m!"organize!: 4-pt config ranks ({idx1}, {idx2}) not recognized as shared-left or shared-outer"

/-- Core lattice driver. Builds + introduces an Arrangement hypothesis
(unique extension), an Arrangement-disjunction (2-ext / 4-pt), or
errors. `nameOverride = none` ⇒ auto-name via `computeArrName`. -/
def runOrganizeLattice (facts : Array ArrFact) (ineqs : Array Expr)
    (nameOverride : Option Name) (goal : MVarId) : TacticM Unit := do
  goal.withContext do
    if facts.isEmpty then
      throwError "organize!: requires at least one Between or Arrangement"
    let mut pool : Array Expr := #[]
    let mut perFactIdx : Array (Array Nat) := #[]
    for f in facts do
      let mut idxs : Array Nat := #[]
      for p in f.points do
        let (k, newPool) ← addPoint pool p
        pool := newPool
        idxs := idxs.push k
      perFactIdx := perFactIdx.push idxs
    let n := pool.size
    if n > Lattice.maxArrangementSize then
      throwError m!"organize!: n={n} exceeds CoeDep cap {Lattice.maxArrangementSize}"
    let mut edges : Array (Nat × Nat) := #[]
    for idxs in perFactIdx do
      for i in [:idxs.size - 1] do
        edges := edges.push (idxs[i]!, idxs[i+1]!)
    let extensions ← match Lattice.enumLinearExtensions n edges with
      | .ok exts   => pure exts
      | .error msg => throwError m!"organize!: {msg}"
    if extensions.isEmpty then
      throwError "organize!: cycle in betweenness constraints (False derivation TODO)"
    let arrName ← match nameOverride with
      | some n => pure n
      | none   => pure (Name.mkSimple (← computeArrName pool edges))
    if extensions.size == 1 then
      let order := extensions[0]!
      let mut rank : Array Nat := Array.replicate n 0
      for k in [:n] do
        rank := rank.set! order[k]! k
      let factRanks := perFactIdx.map (·.map (rank[·]!))
      let arrProof ← buildArrangement facts factRanks n
      let arrType ← inferType arrProof
      let g' ← goal.assert arrName arrType arrProof
      let (_, g') ← g'.intro1P
      replaceMainGoal [g']
    else if extensions.size == 2 ∧ n == 4 ∧ facts.size == 2 then
      let proof ← dispatch4PtSplit pool perFactIdx facts ineqs
      let arrType ← inferType proof
      let g' ← goal.assert arrName arrType proof
      let (_, g') ← g'.intro1P
      replaceMainGoal [g']
    else
      throwError m!"organize!: config (n={n}, extensions={extensions.size}, facts={facts.size}) not yet supported"

/-- `organize! <facts>* (as <ident>)?` — sweep Between / Arrangement
hypotheses plus optional `_ ≠ _` proofs and introduce the maximal
arrangement.

Examples:
- `organize! ABC ABP CneP` introduces `arrAC : Arr [A,B,C,P] ∨ Arr [A,B,P,C]`.
- `organize! ABC BCD` introduces `arrAD : Arrangement [A,B,C,D]`.
- `organize! ABC APC PneB as foo` introduces `foo` instead of `arrAC`.
-/
syntax (name := organizeBangTac)
  "organize!" (ppSpace colGt term:max)* (" as " ident)? : tactic

@[tactic organizeBangTac]
def elabOrganizeBang : Tactic := fun stx => match stx with
  | `(tactic| organize! $hs* $[as $name?]?) => do
    let goal ← getMainGoal
    goal.withContext do
      let mut facts : Array ArrFact := #[]
      let mut ineqs : Array Expr := #[]
      for h in hs do
        let hExpr ← Term.elabTerm h none
        Term.synthesizeSyntheticMVarsNoPostponing
        if let some f ← parseArrFact hExpr then
          facts := facts.push f
        else
          let hTy ← instantiateMVars (← inferType hExpr)
          if hTy.isAppOfArity ``Ne 3 then
            ineqs := ineqs.push hExpr
          else
            throwError m!"organize!: cannot parse `{h}` as Between, Arrangement, or `_ ≠ _`"
      let nameOverride := name?.map (·.getId)
      runOrganizeLattice facts ineqs nameOverride goal
  | _ => throwUnsupportedSyntax

end Geometry.Theory.Arrangement

namespace Geometry.Theory

open Geometry.Ch3.Prop
open Geometry.Ch3.Ex
open Atlas

private lemma cons_get_succ {α} {a : α} {l : List α} {k : Nat}
    (hk : k + 1 < (a :: l).length) :
    (a :: l).get ⟨k + 1, hk⟩ = l.get ⟨k, by simp only [List.length_cons] at hk; omega⟩ := by simp

private lemma get_of_idx_eq {α} (l : List α) {i j : Nat} (hi : i < l.length) (hj : j < l.length)
    (h : i = j) : l.get ⟨i, hi⟩ = l.get ⟨j, hj⟩ := by subst h; rfl

atlas commentary := by
  via lemma 3.0.5
  name "Arrangement.cons — extend a chain by an anchor on the left"
  preface "Given a prior arrangement B-C-... and an anchor A-B-C, the chain A-B-C-... is also an arrangement."

  figure := by
    construction {
      exists A B C D : Point
      assert distinct A B C D
      assert between A B C
      assert between B C D
      construct segAD := segment A D
    }

atlas lemma 3.0.5 "Arrangement.cons"
  {A B C : Point} {rest : List Point}
  (anchor : A - B - C) (arr : Arrangement (B :: C :: rest)) :
    Arrangement (A :: B :: C :: rest) := by
  refine ⟨?_, ?_⟩
  · simp only [List.length_cons]; omega
  rintro ⟨i, hi⟩ ⟨j, hj⟩ ⟨k, hk⟩ hij hjk
  have hij : i < j := hij
  have hjk : j < k := hjk
  simp only [List.length_cons] at hi hj hk
  have hOldLen : (B :: C :: rest).length = rest.length + 2 := by simp
  -- The index shift: prefixing A bumps every old index by 1.
  have shift : ∀ (m : Nat) (hm : m < rest.length + 2),
      (B :: C :: rest).get ⟨m, by rw [hOldLen]; omega⟩ =
      (A :: B :: C :: rest).get ⟨m + 1, by simp only [List.length_cons]; omega⟩ := by
    intro m hm
    rw [cons_get_succ (a := A) (l := B :: C :: rest) (k := m)
          (hk := by simp only [List.length_cons]; omega)]
  have h_AB_at : ∀ m (_ : 2 ≤ m) (hm' : m < rest.length + 3),
      A - B - ((A :: B :: C :: rest).get
        ⟨m, by simp only [List.length_cons]; omega⟩) := by
    intro m hm hm'
    rcases m with _ | _ | _ | m
    · omega
    · omega
    · change A - B - C
      exact anchor
    · have key : B - C - (rest.get ⟨m, by omega⟩) := by
        have h := arr.tri 0 1 (m + 2)
          (by rw [hOldLen]; omega) (by rw [hOldLen]; omega) (by rw [hOldLen]; omega)
          (by omega) (by omega)
        simpa using h
      change A - B - (rest.get ⟨m, by omega⟩)
      exact via corollary 3.3.i ⟨anchor, key⟩
  rcases i with _ | i
  · change A -
      ((A :: B :: C :: rest).get ⟨j, by simp only [List.length_cons]; omega⟩) -
      ((A :: B :: C :: rest).get ⟨k, by simp only [List.length_cons]; omega⟩)
    rcases j with _ | _ | j
    · omega
    · change A - B - ((A :: B :: C :: rest).get _)
      exact h_AB_at k (by omega) hk
    · have hAB : A - B - ((A :: B :: C :: rest).get
          ⟨j + 2, by simp only [List.length_cons]; omega⟩) :=
        h_AB_at (j + 2) (by omega) hj
      have hBjk : B -
          ((A :: B :: C :: rest).get ⟨j + 2, by simp only [List.length_cons]; omega⟩) -
          ((A :: B :: C :: rest).get ⟨k, by simp only [List.length_cons]; omega⟩) := by
        rcases k with _ | k
        · omega
        have h := arr.tri 0 (j + 1) k
          (by rw [hOldLen]; omega) (by rw [hOldLen]; omega) (by rw [hOldLen]; omega)
          (by omega) (by omega)
        have e1 : (B :: C :: rest).get ⟨0, by rw [hOldLen]; omega⟩ = B := by simp
        rw [e1, shift (j + 1) (by omega), shift k (by omega)] at h
        exact h
      exact via corollary 3.3.ii ⟨hAB, hBjk⟩
  · rcases j with _ | j
    · omega
    rcases k with _ | k
    · omega
    have h := arr.tri i j k
      (by rw [hOldLen]; omega) (by rw [hOldLen]; omega) (by rw [hOldLen]; omega)
      (by omega) (by omega)
    rw [shift i (by omega), shift j (by omega), shift k (by omega)] at h
    exact h

atlas commentary := by
  via alternate 3.3
  name "If A-B-C and A-C-D, then A-B-C-D"
  preface ""
  notes "Greenberg relies on figures to disambiguate arrangements, we cannot do that. To accomodate this infacility, we
  have `Arrangements`, which allow for deducing every included ordered triple in the list of points they arrange."

  figure := by
    construction {
      exists A B C D : Point
      assert distinct A B C D
      assert between A B C
      assert between A C D
      construct segAD := segment A D
    }

atlas alternate 3.3 "full chain arrangement from overlapping outer-pair triples"
  {A B C D : Point} (h₁ : A - B - C) (h₂ : A - C - D) : A - B - C - D := by
  have hBCD : B - C - D := via proposition 3.3.i ⟨h₁, h₂⟩
  exact via lemma 3.0.5 h₁ (via lemma 1.0.21 hBCD)

atlas commentary := by
  via lemma 3.0.6
  name "Arrangement.head_swap — replace leading B with X when B-X-C"
  preface "Given Arr[B,C,…] and B-X-C, derive Arr[X,C,…]."

  figure := by
    construction {
      exists B X C D : Point
      assert distinct B X C D
      assert between B X C
      assert between X C D
      construct segBD := segment B D
    }

atlas lemma 3.0.6 "Arrangement.head_swap"
  {B C X : Point} {suf : List Point}
  (arr : Arrangement (B :: C :: suf)) (bxc : B - X - C) :
    Arrangement (X :: C :: suf) := by
  refine ⟨?_, ?_⟩
  · have := arr.three_plus
    simp only [List.length_cons] at this ⊢
    exact this
  rintro ⟨i, hi⟩ ⟨j, hj⟩ ⟨k, hk⟩ hij hjk
  have hij : i < j := hij
  have hjk : j < k := hjk
  simp only [List.length_cons] at hi hj hk
  have hOldLen : (B :: C :: suf).length = suf.length + 2 := by simp
  have arr_BC_suf : ∀ m (hm : m < suf.length),
      B - C - (suf.get ⟨m, hm⟩) := fun m hm => by
    have h := arr.tri 0 1 (m + 2)
      (by rw [hOldLen]; omega) (by rw [hOldLen]; omega) (by rw [hOldLen]; omega)
      (by omega) (by omega)
    simpa using h
  have h_XC_at : ∀ m (hm : m < suf.length),
      X - C - (suf.get ⟨m, hm⟩) := fun m hm =>
    via proposition 3.3.i ⟨bxc, arr_BC_suf m hm⟩
  -- Index-conversion helpers: for any list l ∈ {(X::C::suf), (B::C::suf)} and idx m ≥ 2,
  -- l.get ⟨m, _⟩ = suf.get ⟨m - 2, _⟩.
  have suf_get_of_geq2 :
      ∀ {Y : Point} (m : Nat) (hm : m < suf.length + 2) (hm2 : 2 ≤ m) (hmr : m - 2 < suf.length),
        (Y :: C :: suf).get ⟨m, by simp only [List.length_cons]; omega⟩ = suf.get ⟨m - 2, hmr⟩ := by
    intro Y m hm hm2 hmr
    rw [get_of_idx_eq (Y :: C :: suf) _ (by simp only [List.length_cons]; omega)
        (show m = (m - 2) + 2 from by omega)]
    simp
  rcases Nat.lt_or_ge i 1 with _ | hi'
  · obtain rfl : i = 0 := by omega
    rcases Nat.lt_or_ge j 2 with _ | hj'
    · obtain rfl : j = 1 := by omega
      have hkr : k - 2 < suf.length := by omega
      have e0 : (X :: C :: suf).get ⟨0, by simp only [List.length_cons]; omega⟩ = X := rfl
      have e1 : (X :: C :: suf).get ⟨1, by simp only [List.length_cons]; omega⟩ = C := rfl
      have ek := suf_get_of_geq2 (Y := X) k hk (by omega) hkr
      rw [e0, e1, ek]
      exact h_XC_at (k - 2) hkr
    · have hjr : j - 2 < suf.length := by omega
      have hkr : k - 2 < suf.length := by omega
      have e0 : (X :: C :: suf).get ⟨0, by simp only [List.length_cons]; omega⟩ = X := rfl
      have ej := suf_get_of_geq2 (Y := X) j hj (by omega) hjr
      have ek := suf_get_of_geq2 (Y := X) k hk (by omega) hkr
      rw [e0, ej, ek]
      have hXCj : X - C - (suf.get ⟨j - 2, hjr⟩) := h_XC_at (j - 2) hjr
      have hC_jk : C - (suf.get ⟨j - 2, hjr⟩) - (suf.get ⟨k - 2, hkr⟩) := by
        have h := arr.tri 1 j k
          (by rw [hOldLen]; omega) (by rw [hOldLen]; omega) (by rw [hOldLen]; omega)
          (by omega) (by omega)
        have e1' : (B :: C :: suf).get ⟨1, by rw [hOldLen]; omega⟩ = C := rfl
        have ej' := suf_get_of_geq2 (Y := B) j (by rw [hOldLen] at *; omega) (by omega) hjr
        have ek' := suf_get_of_geq2 (Y := B) k (by rw [hOldLen] at *; omega) (by omega) hkr
        rw [e1', ej', ek'] at h
        exact h
      exact via corollary 3.3.ii ⟨hXCj, hC_jk⟩
  · -- i ≥ 1: triple in old arr at same indices. For m ≥ 1, both lists agree.
    have new_eq_old : ∀ (m : Nat) (_hm_pos : 1 ≤ m) (hm : m < suf.length + 2),
        (B :: C :: suf).get ⟨m, by simp only [List.length_cons]; omega⟩ =
        (X :: C :: suf).get ⟨m, by simp only [List.length_cons]; omega⟩ := by
      intro m _ hm
      rw [get_of_idx_eq (X :: C :: suf) _ (by simp only [List.length_cons]; omega)
            (show m = (m - 1) + 1 from by omega),
          get_of_idx_eq (B :: C :: suf) _ (by simp only [List.length_cons]; omega)
            (show m = (m - 1) + 1 from by omega)]
      simp
    have h := arr.tri i j k
      (by rw [hOldLen]; omega) (by rw [hOldLen]; omega) (by rw [hOldLen]; omega)
      hij hjk
    rw [new_eq_old i (by omega) (by rw [hOldLen] at *; omega),
        new_eq_old j (by omega) (by rw [hOldLen] at *; omega),
        new_eq_old k (by omega) (by rw [hOldLen] at *; omega)] at h
    exact h

atlas commentary := by
  via lemma 3.0.7
  name "Arrangement.insert_head — splice X between leading B and C"
  preface "Given Arr[B,C,…] and B-X-C, derive Arr[B,X,C,…]. Composes head_swap with cons."

  figure := by
    construction {
      exists B X C D : Point
      assert distinct B X C D
      assert between B X C
      assert between X C D
      construct segBD := segment B D
    }

atlas lemma 3.0.7 "Arrangement.insert_head"
  {B C X : Point} {suf : List Point}
  (arr : Arrangement (B :: C :: suf)) (bxc : B - X - C) :
    Arrangement (B :: X :: C :: suf) :=
  via lemma 3.0.5 bxc (via lemma 3.0.6 arr bxc)

atlas commentary := by
  via lemma 3.0.8
  name "If A-B-C and B-C-D, then A-B-C-D"
  preface ""

  figure := by
    construction {
      exists A B C D : Point
      assert distinct A B C D
      assert between A B C
      assert between B C D
      construct segAD := segment A D
    }

atlas lemma 3.0.8 "If A-B-C and B-C-D, then A-B-C-D"
  {A B C D : Point} (h₁ : A - B - C) (h₂ : B - C - D) : A - B - C - D := by
  have hACD : A - C - D := via corollary 3.3.ii ⟨h₁, h₂⟩
  exact via alternate 3.3 h₁ hACD

atlas commentary := by
  via lemma 3.0.9
  name "If A-B-D and B-C-D, then A-B-C-D"
  preface ""

  figure := by
    construction {
      exists A B C D : Point
      assert distinct A B C D
      assert between A B D
      assert between B C D
      construct segAD := segment A D
    }

atlas lemma 3.0.9 "If A-B-D and B-C-D, then A-B-C-D"
  {A B C D : Point} (h₁ : A - B - D) (h₂ : B - C - D) : A - B - C - D := by
  have hCBA : C - B - A := via proposition 3.3.i ⟨h₂.symm, h₁.symm⟩
  have hABC : A - B - C := hCBA.symm
  exact via lemma 3.0.8 hABC h₂

atlas commentary := by
  via lemma 3.0.10
  name "Inner-pair trichotomy: from A-B-C and A-P-C, either A-P-B, P=B, or B-P-C"
  preface ""
  notes "Resolves the topological ambiguity between two points (B, P) that are both strictly between the same outer pair (A, C). The proof case-splits on `P = B`; in the inequality branch it applies axiom B-3 to the three distinct collinear points {A, P, B} and discharges the impossible P-A-B case via corollary 3.3.i + lemma 1.0.18, and the A-B-P case via proposition 3.3.i."

  figure := by
    construction {
      exists A P B C : Point
      assert distinct A P B C
      assert between A P B
      assert between A B C
      construct segAC := segment A C
    }

atlas lemma 3.0.10 "Inner-pair trichotomy: from A-B-C and A-P-C, either A-P-B, P=B, or B-P-C"
  {A B C P : Point} (h₁ : A - B - C) (h₂ : A - P - C) :
    (A - P - B) ∨ (P = B) ∨ (B - P - C) := by
  fixme "This should be in an interpendix"
  by_cases hPeqB : P = B
  · right; left; exact hPeqB
  obtain ⟨distinctABC, colABC, _⟩ := via axiom B.1 h₁
  obtain ⟨distinctAPC, colAPC, _⟩ := via axiom B.1 h₂
  have AneB : A ≠ B := by distinguish
  have AneP : A ≠ P := by distinguish
  have AneC : A ≠ C := by distinguish
  have distinctAPB : distinct A P B := by
    refine ⟨?_⟩
    rw [Finset.card_insert_of_notMem (by simp [AneP, AneB]),
        Finset.card_insert_of_notMem (by simp [hPeqB]),
        Finset.card_singleton]
  have hSameLine : colAPC.line = colABC.line := by
    apply via lemma 2.0.2 AneC
    exact ⟨colAPC.mem A, colABC.mem A, colAPC.mem C, colABC.mem C⟩
  have colAPB : collinear A P B := by
    refine ⟨colABC.line, ?_⟩
    intro q hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with hqA | hqP | hqB
    · rw [hqA]; exact colABC.mem A
    · rw [hqP, ← hSameLine]; exact colAPC.mem P
    · rw [hqB]; exact colABC.mem B
  rcases via axiom B.3 A P B ⟨distinctAPB, colAPB⟩ with
    ⟨APB, _, _⟩ | ⟨_, PAB, _⟩ | ⟨_, _, ABP⟩
  · left; exact APB
  · exfalso
    have BAP : B - A - P := PAB.symm
    have BAC : B - A - C := via corollary 3.3.i ⟨BAP, h₂⟩
    exact via lemma 1.0.18 ⟨h₁, BAC⟩
  · right; right
    exact via proposition 3.3.i ⟨ABP, h₂⟩

macro_rules (kind := obviousArrangement)
  | `(tactic| obvious_arrangement) => `(tactic| organize_auto)

/-! ## Arrangement-disjunction lemmas

When two Between facts leave the linear order on four points
ambiguous, the lattice has exactly two valid extensions. The
following lemmas package the B.3 trichotomy + branch elimination
+ Arrangement construction for the two canonical 4-point
configurations: shared-LEFT pair (3.0.11) and shared-OUTER pair
(3.0.12, lifting 3.0.10 from a Between trichotomy to an Arrangement
disjunction). The `organize!` driver in Phase 3 will dispatch to
these. -/

atlas commentary := by
  via lemma 3.0.11
  name "Shared-left split: A-B-C ∧ A-B-P (∧ C≠P) → Arr[A,B,C,P] ∨ Arr[A,B,P,C]"
  preface ""
  notes "Two Betweens sharing their LEFT pair (A and B). The third point's relative
position to the fourth is the lattice's only ambiguity, so the partial order
admits two linear extensions: [A,B,C,P] (P past C) and [A,B,P,C] (P between B
and C). Proof invokes axiom B-3 on {B, C, P} for the trichotomy, builds each
non-degenerate Arrangement via 3.0.8/3.0.9, and discharges the impossible
C-B-P case by nested B-3 on {A, C, P}."

  figure := by
    construction {
      exists A B C P : Point
      assert distinct A B C P
      assert between A B C
      assert between A B P
      construct segAC := segment A C
      construct segAP := segment A P
    }

atlas lemma 3.0.11 "Shared-left split: A-B-C ∧ A-B-P ∧ C≠P → Arr[A,B,C,P] ∨ Arr[A,B,P,C]"
  {A B C P : Point} (h₁ : A - B - C) (h₂ : A - B - P) (CneP : C ≠ P) :
    Arrangement [A, B, C, P] ∨ Arrangement [A, B, P, C] := by
  obtain ⟨distinctABC, colABC, _⟩ := via axiom B.1 h₁
  obtain ⟨distinctABP, colABP, _⟩ := via axiom B.1 h₂
  have AneB : A ≠ B := by distinguish
  have AneC : A ≠ C := by distinguish
  have AneP : A ≠ P := by distinguish
  have BneC : B ≠ C := by distinguish
  have BneP : B ≠ P := by distinguish
  have distinctBCP : distinct B C P := by
    refine ⟨?_⟩
    rw [Finset.card_insert_of_notMem (by simp [BneC, BneP]),
        Finset.card_insert_of_notMem (by simp [CneP]),
        Finset.card_singleton]
  have hSameLine : colABP.line = colABC.line := by
    apply via lemma 2.0.2 AneB
    exact ⟨colABP.mem A, colABC.mem A, colABP.mem B, colABC.mem B⟩
  have colBCP : collinear B C P := by
    refine ⟨colABC.line, ?_⟩
    intro q hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with hqB | hqC | hqP
    · rw [hqB]; exact colABC.mem B
    · rw [hqC]; exact colABC.mem C
    · rw [hqP, ← hSameLine]; exact colABP.mem P
  rcases via axiom B.3 B C P ⟨distinctBCP, colBCP⟩ with
    ⟨BCP, _, _⟩ | ⟨_, CBP, _⟩ | ⟨_, _, BPC⟩
  · left; exact via lemma 3.0.8 h₁ BCP
  · exfalso
    have distinctACP : distinct A C P := by
      refine ⟨?_⟩
      rw [Finset.card_insert_of_notMem (by simp [AneC, AneP]),
          Finset.card_insert_of_notMem (by simp [CneP]),
          Finset.card_singleton]
    have colACP : collinear A C P := by
      refine ⟨colABC.line, ?_⟩
      intro q hq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with hqA | hqC | hqP
      · rw [hqA]; exact colABC.mem A
      · rw [hqC]; exact colABC.mem C
      · rw [hqP, ← hSameLine]; exact colABP.mem P
    rcases via axiom B.3 A C P ⟨distinctACP, colACP⟩ with
      ⟨ACP, _, _⟩ | ⟨_, CAP, _⟩ | ⟨_, _, APC⟩
    · -- A-C-P: derive B-C-P via prop 3.3.i (ABC, ACP); contradicts CBP via 1.0.18.
      have BCP' : B - C - P := via proposition 3.3.i ⟨h₁, ACP⟩
      exact via lemma 1.0.18 ⟨CBP, BCP'⟩
    · -- C-A-P: apply 3.0.10's trichotomy on (CBP, CAP) → C-A-B ∨ A=B ∨ B-A-P; all impossible.
      rcases via lemma 3.0.10 CBP CAP with CAB | AeqB | BAP
      · exact via lemma 1.0.20 ⟨h₁, CAB⟩
      · exact AneB AeqB
      · exact via lemma 1.0.18 ⟨h₂, BAP⟩
    · -- A-P-C: derive B-P-C via prop 3.3.i (ABP, APC); CPB = BPC.symm contradicts CBP via 1.0.19.
      have BPC' : B - P - C := via proposition 3.3.i ⟨h₂, APC⟩
      exact via lemma 1.0.19 ⟨CBP, BPC'.symm⟩
  · right; exact via lemma 3.0.9 h₁ BPC

atlas commentary := by
  via lemma 3.0.12
  name "Shared-outer split: A-B-C ∧ A-P-C ∧ P≠B → Arr[A,P,B,C] ∨ Arr[A,B,P,C]"
  preface ""
  notes "Lifts lemma 3.0.10's Between trichotomy `(A-P-B) ∨ (P=B) ∨ (B-P-C)` to a
disjunction of full Arrangements. Each non-degenerate branch packages the
known Betweens into the appropriate 4-arrangement via 3.0.8."

  figure := by
    construction {
      exists A P B C : Point
      assert distinct A P B C
      assert between A P B
      assert between A B C
      construct segAC := segment A C
    }

atlas lemma 3.0.12 "Shared-outer split: A-B-C ∧ A-P-C ∧ P≠B → Arr[A,P,B,C] ∨ Arr[A,B,P,C]"
  {A B C P : Point} (h₁ : A - B - C) (h₂ : A - P - C) (PneB : P ≠ B) :
    Arrangement [A, P, B, C] ∨ Arrangement [A, B, P, C] := by
  rcases via lemma 3.0.10 h₁ h₂ with APB | PeqB | BPC
  · -- A-P-B branch: Arr[A,P,B,C] via 3.0.8(APB, P-B-C); P-B-C derived from APB+h₁.
    have PBC' : P - B - C := via proposition 3.3.i ⟨APB, h₁⟩
    left; exact via lemma 3.0.8 APB PBC'
  · exact (PneB PeqB).elim
  · -- B-P-C branch: Arr[A,B,P,C] via 3.0.9(h₁, BPC).
    right; exact via lemma 3.0.9 h₁ BPC

end Geometry.Theory
