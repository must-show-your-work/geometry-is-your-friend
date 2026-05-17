/- Lemmas relating to lines that do not require any theory besides the basic axioms available in Ch1. -/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Insert
import Geometry.Theory.Axioms
import Geometry.Tactics
import Atlas

namespace Geometry.Theory.Line

open Set
open Geometry.Theory

/-- A ray A B is a subset of the line A B -/
atlas lemma 1.0.18 "A ray A B is a subset of the line A B"
  : ray A B ⊆ line A B := by
  intro P PonRay
  simp only [«Betweenness is invariant under endpoint reversal», mem_setOf_eq]
  rcases PonRay with (APB | AeqP | BeqP) | h
  · right; right; left; assumption
  · left; exact AeqP.symm
  · right; left; exact BeqP.symm
  · have ⟨ABP,_⟩ := h
    right; right; right; left; assumption


/-- A segment contains the points that define it -/
atlas lemma 1.0.19 "A segment contains its left-hand defining endpoint"
  : A on segment A B := by tauto

/-- A segment contains the points that define it -/
atlas lemma 1.0.20 "A segment contains its right-hand defining endpoint"
  : B on segment A B := by tauto

/-- A ray contains the points that define it -/
atlas lemma 1.0.21 "A ray contains its left-hand defining endpoint"
  : A on ray A B := by
  simp only [mem_union, mem_setOf_eq, true_or, or_true, ne_eq, not_true_eq_false, false_and, and_false, or_false]

/-- A ray contains the points that define it -/
atlas lemma 1.0.22 "A ray contains its right-hand defining endpoint"
  : B on ray A B := by
  simp only [mem_union, mem_setOf_eq, or_true, ne_eq, not_true_eq_false, and_false, or_false]

/-- A line contains the points that define it -/
atlas lemma 1.0.23 "A line contains its left-hand defining endpoint"
  : A on line A B := (ref lemma 1.0.18) (ref lemma 1.0.21)

/-- A line contains the points that define it -/
atlas lemma 1.0.24 "A line contains its right-hand defining endpoint"
  : B on line A B := (ref lemma 1.0.18) (ref lemma 1.0.22)

/-- A line contains the points that define it -/
atlas lemma 1.0.25 "A line contains both of its defining endpoints"
  : A on line A B ∧ B on line A B := ⟨ref lemma 1.0.23, ref lemma 1.0.24⟩

/-- Author suggests a lemma, "... to prove it, I could first prove a lemma that if three lines
are concurrent, the point at which they meet is unique." p.71 -/
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


/-- We need to be able to establish that two intersecting lines are never parallel -/
atlas lemma 1.0.27 "Two lines sharing a common point are not parallel"
  {L M : Line} {P : Point} : (P on L) -> (P on M) -> (L ∦ M) := by
      intros hPonM hPonL
      unfold Parallel; push_neg
      intro hLMDistinct
      use P


/-- Two lines are coincident iff every point on one is on the other. -/
atlas lemma 1.0.28 "Two lines are equal iff they have exactly the same points"
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
        tauto
     -- Idea: Above, we show that under this case, A,B are on M, so let's construct the unique line AB from AB
     -- This is obviously equal to both L and M, since it's uniquely defined by A and B
     obtain ⟨AB, ⟨AonAB, BonAB⟩, ABuniq⟩ := ref axiom I.1 A B AneB
     have ABeqL := ABuniq L ⟨AonL, BonL⟩
     have ABeqM := ABuniq M ABonM
     rw [ABeqL, ABeqM]


/-- Two lines are distinct iff they have at least one point not in common -/
atlas lemma 1.0.29 "Two lines are distinct iff some point lies on exactly one"
  : ∀ L M : Line,
    L ≠ M ↔ ∃ P, ((P on L) ∧ (P off M)) ∨ ((P off L) ∧ (P on M)) := by
    -- TODO: This is ugly, and it's essentially just !P5.L2, but I couldn't cajole it into place.
    intros L M
    contrapose!
    rw [ref lemma 1.0.28]
    constructor
    intros LMCoincident P
    have LeqM : L = M := by
      rw [ref lemma 1.0.28]; trivial
    rw [LeqM]
    constructor
    tauto
    tauto
    intros h P
    specialize h P
    constructor
    exact h.left
    have hR := h.right
    tauto


end Geometry.Theory.Line
