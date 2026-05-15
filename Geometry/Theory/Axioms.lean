/- The core geometric theory presented in the text is contained here as simple structures/axia taken as needed into
proofs. -/

import Geometry.Tactics
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Defs
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Insert

import Geometry.Theory.Distinct

namespace Geometry.Theory

/-- A point is the fundamental, opaque type we're working with. -/
axiom Point : Type

/-- Greenberg reasons classically throughout. Granting decidable equality on `Point`
    via `Classical.decEq` lets us use `Finset Point` and the associated decidable
    membership/cardinality machinery. -/
noncomputable instance : DecidableEq Point := Classical.decEq Point

/-- Ed: In the text, the author ends up using the 'Line is a Set of points' to define segments, rays, and implicitly
uses the intuitive idea ("A line is the set of collinear points that contain at least two known points"). However, Ch2
uses an opaque 'Line' type and reasons only about it's properties without definition. I try to replicate this in my
implementation of Ch2, but do define it as a set 'up front' -/
@[reducible] def Line := Set Point

-- TODO: Review binding values for all this notation
syntax:50 (name := onNotation) term:51 " on " term:50 : term

-- Macro rules for "on" notation - we need to specify these rules incrementally, so that
-- I can introduce collinear as a definition.
macro_rules (kind := onNotation)
  | `($P on $L) => `($P ∈ $L)


---- COLLINEARITY (FINITE) AND POINTWISE (INFINITE)

-- Collinear: finite set of points on a common line
def Collinear (points : Finset Point) : Prop := ∃ L : Line, ∀ p ∈ points, p ∈ L

-- Syntax: collinear A B C (space-separated)
syntax "collinear" ident+ : term

macro_rules
  | `(collinear $x $xs*) => do
      let allArgs := #[x] ++ xs
      let last := allArgs[allArgs.size - 1]!
      let front := allArgs.pop
      let mut acc ← `((Singleton.singleton $last : Finset _))
      for y in front.reverse do
        acc ← `(insert $y $acc)
      `(Collinear $acc)

-- Pretty printer: TODO restore after Finset-literal unexpander is written

-- Extract the line from collinearity
noncomputable def Collinear.line {points : Finset Point} (h : Collinear points) : Line := Classical.choose h

lemma Collinear.on_line {points : Finset Point} (h : Collinear points) : ∀ p ∈ points, p on h.line := Classical.choose_spec h

@[simp] lemma Collinear.mem {points : Finset Point} (h : Collinear points) (p : Point) (hp : p ∈ points := by simp) :
  p on h.line := h.on_line p hp

example : collinear A B C ↔ ∃ L : Line, A on L ∧ B on L ∧ C on L := by
  constructor
  · intro colABC; use colABC.line;
    exact ⟨colABC.mem A, colABC.mem B, colABC.mem C⟩
  · rintro ⟨L, AonL, BonL, ConL⟩
    use L
    intro P PinABC
    simp only [Finset.mem_insert, Finset.mem_singleton] at PinABC
    rcases PinABC with eq | eq | eq
    repeat rwa [eq]

---- END COLLINEARITY

notation:80 P:81 " off " L:81 => P ∉ L
notation:80 L:81 " has " P:81 => P ∈ L
notation:80 L:81 " avoids " P:81 => P ∉ L

-- -- GEOMETRIC AXIOMS

-- -- -- INCIDENCE GEOMETRY

-- p. 69-70, Ed. The author provides these as very terse statements, I've tried to give informal
-- respellings as documentation.
/--
For any two distinct points P and Q, there exists a unique line L which has P and Q
-/
@[simp] axiom I1 : ∀ P Q : Point, P ≠ Q -> ∃! L : Line, (P on L) ∧ (Q on L)
/-- For any line, there are at least two distinct points on it -/
@[simp] axiom I2 : ∀ L : Line, ∃ A B : Point, A ≠ B ∧ (A on L) ∧ (B on L)
/-- There exists three distinct points not on any single line ("There exists
three non-collinear points", but without mentioning the undefined notion of collinearity) -/
@[simp] axiom I3 : ∃ A B C : Point, (A ≠ B ∧ A ≠ C ∧ B ≠ C) ∧ (∀ (L : Line), (A on L) → (B on L) → (C off L))

/--
p.70 "Three ... lines ... are _concurrent_ if there exists a point incident with all of them"

Ed. Author technically makes this apply to any number of lines, if it ever comes up maybe it's worth
a refactor to any finite set of lines?
-/
@[reducible] def Concurrent (L M N : Line) : Prop :=
    ∃ P : Point, (P on L) ∧ (P on M) ∧ (P on N)

/--
p. 20, "Two lines `l` and `m` are parallel if they do not intersect, i.e., if no point lies on both
of them. We denote this by `l ‖ m`"

p. 70, "Lines `l` and `m` are _parallel_ if they are distinct lines and no point is incident to both
of them."

Ed. This gets defined twice, the definitions are equivalent
-/
@[reducible] def Parallel (L M : Line) : Prop := L ≠ M ∧ ∀ P : Point, ¬((P on L) ∧ (P on M))

notation:20 L " ∥ " M => Parallel L M
notation:20 L " ∦ " M => ¬(Parallel L M)


/- BETWEENNESS GEOMETRY -/

axiom Between : Point -> Point -> Point -> Prop
-- Ed: In the text, the author uses `*`, but Lean reserves that, so I've chosen `-`. `∗` is available, but I don't want
-- to type `\ast` every time.
notation:65 A:66 " - " B:66 " - " C:65 => Between A B C
-- Segment, Ray, Extension, LineThrough

/- Betweenness lets us define line-parts -/
@[reducible] def Segment (A B : Point) := {C | (A - C - B) ∨ A = C ∨ B = C}
@[reducible] def Extension (A B : Point) := {C | A - B - C ∧ A ≠ C ∧ B ≠ C}
@[reducible] def Ray (A B : Point) := (Segment A B) ∪ (Extension A B)
@[reducible] def LineThrough (A B : Point) := {C | C = A ∨ C = B ∨ A - C - B ∨ A - B - C ∨ C - A - B}

syntax:max "segment " term:max term:max : term
syntax:max "ray " term:max term:max : term
syntax:max "extension " term:max term:max : term
syntax:max "line " term:max term:max : term

syntax:1000 "the " "segment " term:max term:max : term
syntax:1000 "the " "ray " term:max term:max : term
syntax:1000 "the " "extension " term:max term:max : term
syntax:1000 "the " "line " term:max term:max : term

-- Re-running
macro_rules (kind := onNotation)
  | `($P on segment $A $B) => `($P ∈ Segment $A $B)
  | `($P on ray $A $B) => `($P ∈ Ray $A $B)
  | `($P on extension $A $B) => `($P ∈ Extension $A $B)
  | `($P on line $A $B) => `($P ∈ LineThrough $A $B)
  | `($P on $L) => `($P ∈ $L)

-- Macro rules for standalone geometric objects (without "the")
macro_rules
  | `(segment $A $B) => `(Segment $A $B)
  | `(ray $A $B) => `(Ray $A $B)
  | `(extension $A $B) => `(Extension $A $B)
  | `(line $A $B) => `(LineThrough $A $B)
  | `(the segment $A $B) => `(Segment $A $B)
  | `(the ray $A $B) => `(Ray $A $B)
  | `(the extension $A $B) => `(Extension $A $B)
  | `(the line $A $B) => `(LineThrough $A $B)



/--
p.108a "If A - B - C, then A,B,C are distinct points on the same line...
-/
@[simp] axiom B1a {A B C : Point} : A - B - C -> distinct A B C ∧ collinear A B C


/--
p.108b ... and [A - B - C iff] C - B - A.""

Ed. Note, I separated these parts of the axiom to make rewriting
a bit easier. The author even notes, "The second part (C * B * A) makes the obvious remark
that 'betwen A and C' means the same as 'between C and A'" Making it a separate axiom means
I won't have to dig it out of the pile of parts that is 1a.
-/
@[simp] axiom B1b {A B C : Point} : A - B - C ↔ C - B - A


/--
p.108 "Given any two distinct points B and D, there exist points A, C, and E lying on →ₗBD such that
A * B * D, B * C * D, and B * D * E".

Ed. I like to call this the 'density' axiom because, used recursively, it posits
something like the density of rationals -- for any two distinct points on a
line, there is always a point between them.
-/
@[simp] axiom B2 : ∀ B D : Point, B ≠ D ->
  ∃ A C E : Point, collinear A B C D E ∧ distinct A B C D E ∧ (A - B - D) ∧ (B - C - D) ∧ (B - D - E)


/-- Construct a point 'to the left' of points BD on the induced line B D -/
lemma B2.left : ∀ B D : Point, B ≠ D -> ∃ A : Point, collinear A B D ∧ distinct A B D ∧ (A - B - D) := by
      intro B D BneD
      have ⟨A, _, _, colABCDE, distinctABCDE, ABD, _, _⟩ := B2 B D BneD
      use A
      simp_all only [ne_eq, B1b, B1a, and_self]

/-- Construct a point 'in between' points BD on the induced line B D -/
lemma B2.center : ∀ B D : Point, B ≠ D -> ∃ C : Point, collinear B C D ∧ distinct B C D ∧ (B - C - D) := by
      intro B D BneD
      have ⟨_, C, _, colABCDE, distinctABCDE, _, BCD, _⟩ := B2 B D BneD
      use C
      simp_all only [ne_eq, B1b, B1a, and_self]


/-- Construct a point 'to the right' points BD on the induced line B D -/
lemma B2.right : ∀ B D : Point, B ≠ D -> ∃ E : Point, collinear B D E ∧ distinct B D E ∧ (B - D - E) := by
      intro B D BneD
      have ⟨_, _, E, colABCDE, distinctABCDE, _, _, BDE⟩ := B2 B D BneD
      use E
      simp_all only [ne_eq, B1b, B1a, and_self]

/-- p.108 "If A, B, and C are three distinct points lying on the same line, then
 one and only one of the points is between the other two."
-/
@[simp] axiom B3 : ∀ A B C : Point, distinct A B C ∧ collinear A B C ->
  ( (A - B - C) ∧ ¬(B - A - C) ∧ ¬(A - C - B)) ∨
  (¬(A - B - C) ∧  (B - A - C) ∧ ¬(A - C - B)) ∨
  (¬(A - B - C) ∧ ¬(B - A - C) ∧  (A - C - B))

/--
p.110 "Definition. Let L be any line, and A and B points that do not lie on L. If A = B or if the segment A B
contains no points that lie on L, we say that A and B are _on the same side_ of L; whereas, if A ≠ B and segment A B
does intersect L, we say that A and B are _on opposite sides_ of L (see Figure 3.6). The law of the excluded middle
(Logic Rule 10) tells us that A and B are either on the same side or on opposite sides of L"
-/
@[reducible] def SameSide (A B : Point) (L : Line)
  := (A off L) ∧ (B off L) ∧ ((A = B) ∨ (∀ P : Point, (P on segment A B) -> (L avoids P)))

/--
"Splits" and "Guards", L "splits" A and B if A and B are on opposite sides of the 'wall' L, it 'guards'
them if they are both on the same side of the wall (we presume all points are allied with other points
on their side of the line).
-/
notation:20 L " splits " A " and " B => ¬(SameSide A B L)
notation:20 L " guards " A " and " B => SameSide A B L

/--
Ed. The author refers to the law of the excluded middle, Lean does not include it by default and
generally I want to avoid including it everywhere, this is a limited application of it which
should help our purpose.
-/
@[simp] axiom LotEMGuards : (L splits A and B) ∨ (L guards A and B)

/--
p.110 "Betweenness Axiom 4 (Plane Separation). For every line L and for any
three points A, B, and C not on L: (i) If A and B are on the same side of L and
if B and C are on the same side of L, the A and C are on the same side of L..."
-/
@[simp] axiom B4i {A B C : Point} {L : Line} :
  (L avoids A) ∧ (L avoids B) ∧ (L avoids C) ->
  (L guards A and B) ∧ (L guards B and C) -> (L guards A and C)
/--
"... (ii) If A and B are on opposite sides of L and if B and C are opposite
sides of L, then A and C are on the same side of L."
-/
@[simp] axiom B4ii {A B C : Point} {L : Line} :
  (L avoids A) ∧ (L avoids B) ∧ (L avoids C) ->
  (L splits A and B) ∧ (L splits B and C) -> (L guards A and C)

@[reducible] def Intersects (L M : Line) (X : Point) : Prop := L ∩ M = {X}

/-- Bare form of `L intersects M` — asserts there is a (unique) point shared by
    both sets. Kept as an opaque `def` so the goal stays readable; the unexpander
    below renders this as `L intersects M` in proof states. -/
def IntersectsSome (L M : Set Point) : Prop := ∃ X, L ∩ M = {X}

/-- Extract the intersection witness: `L intersects M → ∃ X, L intersects M at X`.
    This is the main consumer of a bare `intersects` hypothesis. -/
lemma IntersectsSome.intersection_point {L M : Set Point} (h : IntersectsSome L M) :
    ∃ X, L ∩ M = {X} := h

-- Syntax for "L intersects M at X" (specific intersection point) and the bare
-- form "L intersects M" asserting a unique shared point exists.
syntax:50 (name := intersectsAt) term:51 " intersects " term:51 " at " term:50 : term
syntax:50 (name := intersectsBare) term:51 " intersects " term:51 : term

macro_rules (kind := intersectsAt)
  | `($L intersects $M at $X) => `(Intersects $L $M $X)

macro_rules (kind := intersectsBare)
  | `($L intersects $M) => `(IntersectsSome $L $M)

-- Pretty-print `IntersectsSome L M` as `L intersects M` so the goal stays readable
@[app_unexpander IntersectsSome]
def IntersectsSome.unexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $L $M) => `($L intersects $M)
  | _ => throw ()

/-- `normalize_eq` walks the local context and flips `=` / `≠` hypotheses between
    free variables so the LHS comes lex-before the RHS by user-name. Useful when
    a downstream tactic (`simp`, `tauto`) doesn't know about `Ne.symm` / `Eq.symm`
    and is stuck on an inequality whose orientation is "backwards". -/
syntax "normalize_eq" : tactic

open Lean Meta Elab.Tactic in
elab_rules : tactic
  | `(tactic| normalize_eq) => withMainContext do
    -- Snapshot the list of hypotheses to flip; applying them mutates the local
    -- context, so collect first and apply after.
    let lctx ← getLCtx
    let mut toFlip : Array (Name × Bool) := #[]  -- (hypothesis name, isEq?)
    for ldecl in lctx do
      if ldecl.isImplementationDetail then continue
      let ty ← instantiateMVars ldecl.type
      let (isEq, a?, b?) ←
        if ty.isAppOfArity ``Eq 3 then
          pure (true, some (ty.getArg! 1), some (ty.getArg! 2))
        else if ty.isAppOfArity ``Ne 3 then
          pure (false, some (ty.getArg! 1), some (ty.getArg! 2))
        else
          pure (false, none, none)
      match a?, b? with
      | some a, some b =>
        if a.isFVar && b.isFVar then
          let aName := (← a.fvarId!.getUserName).toString
          let bName := (← b.fvarId!.getUserName).toString
          if aName > bName then
            toFlip := toFlip.push (ldecl.userName, isEq)
      | _, _ => pure ()
    for (hName, isEq) in toFlip do
      let hIdent := mkIdent hName
      let symIdent := mkIdent (if isEq then ``Eq.symm else ``Ne.symm)
      evalTactic (← `(tactic| replace $hIdent:ident := $symIdent:ident $hIdent:ident))

/-- Attempts to unfold any geometric objects in the vicinity and eliminate booleans
 and the like. Tries to capture the author's intuition for 'by definition' in the text.

 The last alternative handles Finset literal equality (`{A,B,C} = {C,A,B}` etc.) by
 reducing to membership and tautology — convenient since Finsets are unordered.

 `normalize_eq` runs first to canonicalize `=` / `≠` orientations so `simp_all` can
 close hypotheses regardless of which side they were originally written on. -/
macro "obvious" : tactic =>
  `(tactic| (
      normalize_eq
      first
      | (simp_all only [
          -- set
          Set.mem_setOf_eq, Set.mem_union, Set.mem_inter_iff,
          Set.mem_singleton_iff,
          -- finset
          Finset.mem_insert, Finset.mem_singleton, Finset.mem_erase, Finset.notMem_empty,
          -- line parts
          Segment, Ray, Extension, LineThrough,
          -- betweenness normalizing
          B1b,
          -- propositional stuff
          ne_eq, true_or, or_true, false_or, or_false, or_self,
          true_and, and_true, false_and, and_false, and_self,
          not_true_eq_false, not_false_eq_true, not_or, not_and, not_not
        ]; done)
      | (simp only [Segment, Ray, Extension, LineThrough]; tauto)
      | (unfold Segment Ray Extension LineThrough at *; tauto)
      | (ext; simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_erase, ne_eq]; tauto)))

macro "obvious" : term => `(by obvious)

/-- `clearly P := by body` introduces `P` as a fact for the rest of the proof, having
    discharged the negation branch — i.e. the body proves the main goal under the
    assumption `¬P`. The reading is: "clearly P, because if not, the goal is immediate
    (`body`); proceeding under `P`".

    Supported shapes for `P` (auto-named hypotheses derived from the identifiers):
    - `A ≠ B`: rest of proof gets `AneB : A ≠ B`; body sees `AeqB : A = B`.
    - `A = B`: rest of proof gets `AeqB : A = B`; body sees `AneB : A ≠ B`.
    - `P on L`: rest of proof gets `PonL : P on L`; body sees `PoffL : P off L`.
    - `P off L`: rest of proof gets `PoffL : P off L`; body sees `PonL : P on L`. -/
syntax "clearly " term " := " "by " tacticSeq : tactic
syntax "clearly " term : tactic

/-- Derive an auto-name component from a term used in a `clearly` clause.
    Identifiers map to their user-name; line-part expressions get short
    capitalized prefixes (`segment A B` → `SegAB`, `line A B` → `LineAB`, etc.). -/
private def clearlyTermName (s : Lean.Syntax) : Lean.MacroM String := do
  match s with
  | `($id:ident) => return id.getId.toString
  | `(segment $A:ident $B:ident) => return s!"Seg{A.getId}{B.getId}"
  | `(ray $A:ident $B:ident) => return s!"Ray{A.getId}{B.getId}"
  | `(extension $A:ident $B:ident) => return s!"Ext{A.getId}{B.getId}"
  | `(line $A:ident $B:ident) => return s!"Line{A.getId}{B.getId}"
  | _ => Lean.Macro.throwError "clearly: cannot derive an auto-name from this term"

-- `macro_rules` (rather than `elab_rules`) expansion keeps the resulting tactics
-- visible to the LSP. However, see FIXME below.
--
-- FIXME: LSP doesn't render the body-side hypothesis (e.g. `ConL` inside a
-- `clearly C off L := by ...` block) in the goal panel at intermediate lines of
-- the body, even though it IS in scope (usable in the proof and visible via
-- `trace_state`). The other-side hypothesis (e.g. `CoffL` on the line after the
-- `clearly` block) renders fine. Suspected cause: macro-introduced `rcases` /
-- `case inl =>` tokens get synthetic source positions that the LSP's info-tree
-- walker doesn't query against. Workaround: put a `trace_state` at the body's
-- start to confirm the hypothesis is there.
macro_rules
  | `(tactic| clearly $prop) => `(tactic| clearly $prop := by obvious)
  | `(tactic| clearly $lhs ≠ $rhs := by $body) => do
    let lName ← clearlyTermName lhs
    let rName ← clearlyTermName rhs
    let eqIdent := Lean.mkIdent (.mkSimple s!"{lName}eq{rName}")
    let neIdent := Lean.mkIdent (.mkSimple s!"{lName}ne{rName}")
    `(tactic| (
      rcases Classical.em ($lhs = $rhs) with $eqIdent:ident | $neIdent:ident
      case inl => $body))
  | `(tactic| clearly $lhs = $rhs := by $body) => do
    let lName ← clearlyTermName lhs
    let rName ← clearlyTermName rhs
    let eqIdent := Lean.mkIdent (.mkSimple s!"{lName}eq{rName}")
    let neIdent := Lean.mkIdent (.mkSimple s!"{lName}ne{rName}")
    `(tactic| (
      rcases Classical.em ($lhs = $rhs) with $eqIdent:ident | $neIdent:ident
      case inr => $body))
  | `(tactic| clearly $P on $L := by $body) => do
    let pName ← clearlyTermName P
    let lName ← clearlyTermName L
    let onIdent := Lean.mkIdent (.mkSimple s!"{pName}on{lName}")
    let offIdent := Lean.mkIdent (.mkSimple s!"{pName}off{lName}")
    `(tactic| (
      rcases Classical.em ($P ∈ $L) with $onIdent:ident | $offIdent:ident
      case inr => $body))
  | `(tactic| clearly $P off $L := by $body) => do
    let pName ← clearlyTermName P
    let lName ← clearlyTermName L
    let onIdent := Lean.mkIdent (.mkSimple s!"{pName}on{lName}")
    let offIdent := Lean.mkIdent (.mkSimple s!"{pName}off{lName}")
    `(tactic| (
      rcases Classical.em ($P ∈ $L) with $onIdent:ident | $offIdent:ident
      case inl => $body))


end Geometry.Theory
