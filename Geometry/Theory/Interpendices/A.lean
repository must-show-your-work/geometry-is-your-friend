import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Insert
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Insert
import Geometry.Theory.Axioms
import Geometry.Tactics
import Atlas

/-!
# Interpendix A — axiom-derivable theorems
-/

namespace Set

open Set
open Atlas

atlas commentary := by
  ref lemma 0.0.5
  name "Disjoint-union subset cancellation"
  preface "If S is disjoint from T and V, then S ∪ T ⊆ S ∪ V implies T ⊆ V"

atlas lemma 0.0.5 "Disjoint-union subset cancellation"
  : ∀ S T V : Set α, S ∪ T ⊆ S ∪ V ∧ S ∩ T = ∅ ∧ S ∩ V = ∅ -> T ⊆ V := by
  intro S T V ⟨SuTsubSuV, SintTempty, SintVempty⟩ e eInT
  have eInSuT : e ∈ S ∪ T := (mem_union e S T).mpr (Or.inr eInT)
  have eInSuV : e ∈ S ∪ V := (mem_union e S V).mpr (SuTsubSuV eInSuT)
  rcases eInSuV with eInS | eInV
  · exact absurd ⟨eInS, eInT⟩ (Set.eq_empty_iff_forall_notMem.mp SintTempty e)
  · exact eInV


atlas commentary := by
  ref lemma 0.0.6
  name "Disjoint-union equality cancellation"
  preface "If S is disjoint from T and V, then S ∪ T = S ∪ V implies T = V (TODO: may be iff)"

atlas lemma 0.0.6 "Disjoint-union equality cancellation"
  : ∀ S T V : Set α,  S ∪ T = S ∪ V ∧ S ∩ T = ∅ ∧ S ∩ V = ∅ -> T = V := by
  intro S T V ⟨SuTeqSuV, SintTempty, SintVempty⟩
  comment "This is a cool technique, similar to the 'by symmetry' or 'up to variable naming'."
  suffices h : ∀ A B : Set α, S ∪ A ⊆ S ∪ B ∧ S ∩ A = ∅ ∧ S ∩ B = ∅ → A ⊆ B by
    exact Subset.antisymm
      (h T V ⟨(Eq.subset SuTeqSuV), SintTempty, SintVempty⟩)
      (h V T ⟨(Eq.subset SuTeqSuV.symm), SintVempty, SintTempty⟩)
  exact ref lemma 0.0.5 S

end Set


namespace Geometry.Theory

open Set
open Geometry.Theory
open Atlas

atlas commentary := by
  ref lemma 1.0.5
  name "Density axiom witness: a point left of two distinct points"
  preface "Construct a point 'to the left' of points BD on the induced line B D"

atlas lemma 1.0.5 "Density axiom witness: a point left of two distinct points"
  : ∀ B D : Point, B ≠ D -> ∃ A : Point, collinear A B D ∧ distinct A B D ∧ (A - B - D) := by
      intro B D BneD
      have ⟨A, _, _, colABCDE, distinctABCDE, ABD, _, _⟩ := ref axiom B.2 B D BneD
      use A
      obvious


atlas commentary := by
  ref lemma 1.0.6
  name "Density axiom witness: a point between two distinct points"
  preface "Construct a point 'in between' points BD on the induced line B D"

atlas lemma 1.0.6 "Density axiom witness: a point between two distinct points"
  : ∀ B D : Point, B ≠ D -> ∃ C : Point, collinear B C D ∧ distinct B C D ∧ (B - C - D) := by
      intro B D BneD
      have ⟨_, C, _, colABCDE, distinctABCDE, _, BCD, _⟩ := ref axiom B.2 B D BneD
      use C
      obvious


atlas commentary := by
  ref lemma 1.0.7
  name "Density axiom witness: a point right of two distinct points"
  preface "Construct a point 'to the right' points BD on the induced line B D"

atlas lemma 1.0.7 "Density axiom witness: a point right of two distinct points"
  : ∀ B D : Point, B ≠ D -> ∃ E : Point, collinear B D E ∧ distinct B D E ∧ (B - D - E) := by
      intro B D BneD
      have ⟨_, _, E, colABCDE, distinctABCDE, _, _, BDE⟩ := ref axiom B.2 B D BneD
      use E
      obvious

namespace Point

atlas commentary := by
  ref lemma 1.0.11
  name "For every Point there exists at least one distinct Point"
  preface "For every Point, there is at least one point that isn't that point."

atlas lemma 1.0.11 "For every Point there exists at least one distinct Point"
  : ∀ P : Point, ∃ Q : Point, P ≠ Q := by
    intro P
    obtain ⟨A, B, C, hDistinct, _⟩ := ref axiom I.3
    idea "There is a configuration of 3 non-colinear points. Either P is one of those points, or it's none of
    them. If it's one of them, there are two other points distinct from P; if it's not one of them, then
    there are three distinct points."
    by_cases hSupposePeqA : P = A -- ∨ P = B ∨ P = C
    rw [<- hSupposePeqA] at hDistinct
    use B
    exact hDistinct.left
    use A

end Point

namespace Collinear

/-- collinear points can be used in place of a line by using the induced line -/
noncomputable instance : Coe {s : Finset Point // Collinear s} Line where
  coe := fun ⟨_, h⟩ => h.line

noncomputable instance collinearCoe {points : Finset Point} (h : Collinear points) : CoeDep (Collinear points) h Line where
  coe := h.line

-- Natural projections on Collinear values — not book content, not atlas'd.

/-- a subset of a collinear set of points is collinear -/
@[simp] lemma subset {s s' : Finset Point} (h : Collinear s) (hs : s' ⊆ s) : Collinear s' :=
  ⟨h.line, fun p hp => h.on_line p (hs hp)⟩

/-- Cast `Collinear` between propositionally-equal Finsets — Finsets are unordered,
    so two literals describing the same elements are equal even when they don't unify
    definitionally. Useful when stitching together facts produced under different
    insertion orders (e.g. `(ref axiom B.1 (CAB : C - A - B)).collinear` yields
    `Collinear {C, A, B}` but a consumer wants `Collinear {A, B, C}`). -/
lemma of_eq {s t : Finset Point} (c : Collinear s) (h : s = t) : Collinear t := h ▸ c

atlas commentary := by
  ref lemma 1.0.14
  name "Any two distinct points are collinear"
  preface "There is a line between any two points, so by definition any two points are collinear"

atlas lemma 1.0.14 "Any two distinct points are collinear"
  : A ≠ B -> collinear A B := by
  intro AneB
  have ⟨L, ⟨AonL, BonL⟩, _h⟩ := ref axiom I.1 A B AneB
  unfold Collinear
  use L
  intro P PinSub
  simp only [Finset.mem_insert, Finset.mem_singleton] at PinSub
  rcases PinSub with eq | eq
  repeat rwa [eq]

attribute [simp] «Any two distinct points are collinear»

/-- Collinearity is independent of underlying set representation; Finsets with the
    same membership are equal, so this collapses to reflexivity through `Finset.ext`. -/
@[simp] lemma order_irrelevance {S T : Finset Point}
    (leftCol : Collinear S)
    (samePoints : ∀ p, p ∈ S ↔ p ∈ T := by aesop) :
  Collinear T := by
  obtain ⟨L, hL⟩ := leftCol
  use L
  intro p hp
  exact hL p ((samePoints p).mpr hp)

atlas lemma 1.0.16 "Collinearity ignores trailing duplicate point (A B B ↔ A B)"
  (A B : Point) : collinear A B B ↔ collinear A B := by
  constructor
  · intro h; exact Collinear.order_irrelevance h (by intro p; simp [Finset.mem_insert, Finset.mem_singleton])
  · intro h; exact Collinear.order_irrelevance h (by intro p; simp [Finset.mem_insert, Finset.mem_singleton])

attribute [simp] «Collinearity ignores trailing duplicate point (A B B ↔ A B)»

atlas lemma 1.0.17 "Collinearity ignores interleaved duplicate point (B A B ↔ A B)"
  (A B : Point) : collinear B A B ↔ collinear A B := by
  constructor
  · intro h; exact Collinear.order_irrelevance h (by intro p; simp [Finset.mem_insert, Finset.mem_singleton]; try obvious)
  · intro h; exact Collinear.order_irrelevance h (by intro p; simp [Finset.mem_insert, Finset.mem_singleton]; try obvious)

attribute [simp] «Collinearity ignores interleaved duplicate point (B A B ↔ A B)»

end Collinear

namespace Line

atlas commentary := by
  ref lemma 1.0.18
  name "A ray A B is a subset of the line A B"
  preface "A ray A B is a subset of the line A B"

atlas lemma 1.0.18 "A ray A B is a subset of the line A B"
  : (ray A B : Set Point) ⊆ (line A B : Set Point) := by
  intro P PonRay
  rcases PonRay with (APB | AeqP | BeqP) | h
  · right; right; left; assumption
  · left; exact AeqP.symm
  · right; left; exact BeqP.symm
  · have ⟨ABP,_⟩ := h
    right; right; right; left; assumption


atlas commentary := by
  ref lemma 1.0.26
  page 71
  name "Three pairwise-distinct concurrent lines meet at a unique point"
  preface "Author suggests a lemma, \"... to prove it, I could first prove a lemma that if three lines
are concurrent, the point at which they meet is unique.\""

atlas lemma 1.0.26 "Three pairwise-distinct concurrent lines meet at a unique point"
  : L ≠ M ∧ M ≠ N ∧ L ≠ N ->
        Concurrent L M N ->
        ∃! P : Point,
        (P on L) ∧ (P on M) ∧ (P on N)
:= by
    intros hDistinct hConcurrent
    unfold Concurrent at *
    obtain ⟨P, hPonL, hPonM, hPonN⟩ := hConcurrent
    refine ⟨P, ?cEx, ?cUniq⟩
    -- existence
    exact ⟨hPonL, hPonM, hPonN⟩
    -- uniqueness
    intro Q ⟨hQonL, hQonM, hQonN⟩
    by_contra! hNeg
    have ⟨PQ, _, hPQUniq⟩ := ref axiom I.1 P Q hNeg.symm
    have hPQisL := hPQUniq L ⟨hPonL, hQonL⟩
    have hPQisM := hPQUniq M ⟨hPonM, hQonM⟩
    have hLeqM : L = M := by
        rw [hPQisL, hPQisM]
    have hLneqM : L ≠ M := hDistinct.left
    contradiction


atlas commentary := by
  ref lemma 1.0.28
  name "Line Extensionality"
  preface "Two lines are coincident iff every point on one is on the other."

atlas lemma 1.0.28 "Line Extensionality"
  : ∀ L M : Line,
     L = M ↔ ∀ P : Point, (P on L) ↔ (P on M) := by
     intros L M
     constructor
     -- Forward Case
     intros LeqM P
     rw [LeqM]
     -- Backward Case
     intro hAllPonLonM
     obtain ⟨A,B,AneB,AonL,BonL⟩ := ref axiom I.2 L
     obtain ⟨C,D,CneD,ConM,DonM⟩ := ref axiom I.2 M
     have ABonM : (A on M) ∧ (B on M) := by
        have AonM := hAllPonLonM A
        have BonM := hAllPonLonM B
        obvious
     idea "Above, we show that under this case, A,B are on M, so let's construct the unique line AB from AB
     This is obviously equal to both L and M, since it's uniquely defined by A and B"
     obtain ⟨AB, ⟨AonAB, BonAB⟩, ABuniq⟩ := ref axiom I.1 A B AneB
     have ABeqL := ABuniq L ⟨AonL, BonL⟩
     have ABeqM := ABuniq M ABonM
     rw [ABeqL, ABeqM]

attribute [obvious] «Line Extensionality»


atlas commentary := by
  ref lemma 1.0.29
  name "Two lines are distinct iff some point lies on exactly one"
  preface "Two lines are distinct iff they have at least one point not in common"

atlas lemma 1.0.29 "Two lines are distinct iff some point lies on exactly one"
  : ∀ L M : Line,
    L ≠ M ↔ ∃ P, ((P on L) ∧ (P off M)) ∨ ((P off L) ∧ (P on M)) := by
    intros L M
    contrapose!
    constructor
    · intro LeqM _; rw [LeqM]; obvious
    · intro hP
      rw [«Line Extensionality»]
      intro P; obtain ⟨PonLM, _⟩ := hP P
      obvious

end Line

namespace Intersection

atlas commentary := by
  ref lemma 1.0.30
  name "Two pointed intersections of the same line pair share their point"
  preface "If two lines intersect, their intersection is unique."
  tags ["obvious.intersects"]

atlas lemma 1.0.30 "Two pointed intersections of the same line pair share their point"
  : (L intersects M at X) ∧ (L intersects M at Y) -> X = Y := by
  unfold Intersects
  intro ⟨LMatX, LMatY⟩
  rw [LMatX] at LMatY
  exact Line.singleton_eq_singleton.mp LMatY


atlas commentary := by
  ref lemma 1.0.31
  name "Pointed intersection is symmetric in its line arguments"
  preface "L intersects M is the same as M intersects L."
  tags ["obvious.intersects"]

atlas lemma 1.0.31 "Pointed intersection is symmetric in its line arguments"
  : (L intersects M at X) ↔ (M intersects L at X) := by
  unfold Intersects
  refine Eq.congr ?_ rfl
  exact Line.inter_comm L M

attribute [symm] «Pointed intersection is symmetric in its line arguments»

/-- Dot-notation wrapper: `h.symm` swaps the line args of an `L intersects M at X`
    hypothesis. Picks up the `@[symm]` Iff form above via projection. -/
@[symm] def Intersects.symm {L M : Line} {X : Point}
  (h : L intersects M at X) : M intersects L at X :=
  («Pointed intersection is symmetric in its line arguments»).mp h


atlas commentary := by
  ref lemma 1.0.32
  name "A pointed intersection's witness point lies on the left line"
  preface "If L intersects M at X, then X is on L"
  tags ["obvious.intersects"]

atlas lemma 1.0.32 "A pointed intersection's witness point lies on the left line"
  : (L intersects M at X) -> (X on L) := by
  unfold Intersects
  intro LMintX
  have XinLintM : X ∈ L ∩ M := by rw [LMintX]; simp
  exact (Line.mem_inter.mp XinLintM).1


atlas commentary := by
  ref lemma 1.0.33
  name "A pointed intersection's witness point lies on the right line"
  preface "If L intersects M at X, then X is on M"
  tags ["obvious.intersects"]

atlas lemma 1.0.33 "A pointed intersection's witness point lies on the right line"
  : (L intersects M at X) -> (X on M) := by
  unfold Intersects
  intro LMintX
  have XinLintM : X ∈ L ∩ M := by rw [LMintX]; simp
  exact (Line.mem_inter.mp XinLintM).2


atlas commentary := by
  ref lemma 1.0.34
  name "A pointed intersection's witness point lies on both lines"
  preface "If L intersects M at X, then X is on L and M"

atlas lemma 1.0.34 "A pointed intersection's witness point lies on both lines"
  : (L intersects M at X) -> (X on L) ∧ (X on M) := by intro inter; exact ⟨ref lemma 1.0.32 inter, ref lemma 1.0.33 inter⟩


atlas commentary := by
  ref lemma 1.0.35
  name "On distinct lines crossing at X every other point on L is off M"
  preface "If L intersects M at X, then forall P not equal to X, if P on L, then P off M."

atlas lemma 1.0.35 "On distinct lines crossing at X every other point on L is off M"
  : (L ≠ M) ∧ (L intersects M at X) -> (∀ P : Point, (P ≠ X) ∧ (P on L) -> (P off M)) := by
  intro ⟨LneM, LintMatX⟩ P ⟨PneX, PonL⟩
  unfold Intersects at LintMatX
  by_contra! PonM
  have PinLintM : P ∈ (L ∩ M) := ⟨PonL, PonM⟩
  rw [LintMatX] at PinLintM
  contradiction

end Intersection

namespace Betweenness

atlas commentary := by
  ref lemma 1.0.36
  name "Betweenness contradiction: A-B-C cannot coexist with B-A-C"
  preface "With respect to a fixed point, every pair of points can be said to either be 'to the left' or 'to the right' of
one another"

atlas lemma 1.0.36 "Betweenness contradiction: A-B-C cannot coexist with B-A-C"
  : A - B - C ∧ B - A - C -> False := by
  intro ⟨ABC, _⟩
  obtain ⟨distinctABC, colABC, _⟩ := ref axiom B.1 ABC
  rcases ref axiom B.3 A B C ⟨distinctABC, colABC⟩ with ⟨ABC, nBAC, nACB⟩ | ⟨nABC,BAC,nACB⟩ | ⟨nABC,nBAC,ACB⟩
  repeat contradiction


atlas commentary := by
  ref lemma 1.0.37
  name "Betweenness contradiction: A-B-C cannot coexist with A-C-B"
  preface "With respect to a fixed point, every pair of points can be said to either be 'to the left' or 'to the right' of
one another"

atlas lemma 1.0.37 "Betweenness contradiction: A-B-C cannot coexist with A-C-B"
  : A - B - C ∧ A - C - B -> False := by
  intro ⟨ABC, _⟩
  obtain ⟨distinctABC, colABC, _⟩ := ref axiom B.1 ABC
  rcases ref axiom B.3 A B C ⟨distinctABC, colABC⟩ with ⟨ABC, nBAC, nACB⟩ | ⟨nABC,BAC,nACB⟩ | ⟨nABC,nBAC,ACB⟩
  repeat contradiction


atlas commentary := by
  ref lemma 1.0.38
  name "Betweenness contradiction: A-B-C cannot coexist with C-A-B"
  preface "With respect to a pair of fixed points, another point is either 'to the left' or 'to the right' of the pair"

atlas lemma 1.0.38 "Betweenness contradiction: A-B-C cannot coexist with C-A-B"
  : A - B - C ∧ C - A - B -> False := by
  intro ⟨ABC, CAB⟩
  obtain ⟨distinctABC, colABC, _⟩ := ref axiom B.1 ABC
  rcases ref axiom B.3 A B C ⟨distinctABC, colABC⟩ with ⟨_, nBAC, _⟩ | ⟨nABC, _, _⟩ | ⟨nABC, _, _⟩
  · exact nBAC CAB.symm
  · exact nABC ABC
  · exact nABC ABC

end Betweenness

structure Arrangement (pts : List Point) : Prop where
  three_plus : pts.length ≥ 3
  ordered_triple : ∀ (i j k : Fin pts.length),
    i.val < j.val → j.val < k.val →
    Between (pts.get i) (pts.get j) (pts.get k)

atlas commentary := by
  ref lemma 1.0.39
  name "Three-point arrangement from a single between"
  preface "A single A-B-C betweenness packages directly as an Arrangement [A, B, C]."

atlas lemma 1.0.39 "Three-point arrangement from a single between"
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

end Geometry.Theory.Arrangement
