import Geometry.Tactics

import Geometry.Theory.Axioms
import Geometry.Theory.Ch1
import Geometry.Theory.Line.Ch1
import Atlas

import Geometry.Ch2.Prop.P1

namespace Geometry.Ch2.Prop

open Geometry.Theory
open Atlas


atlas commentary := by
  ref proposition 2.2
  page 71
  name "Three distinct lines exist that are not concurrent"
  preface "There exist three distinct lines that are not concurrent."

atlas proposition 2.2 "Three distinct lines exist that are not concurrent"
  : ∃ L M N : Line, (L ≠ M ∧ M ≠ N ∧ L ≠ N) ∧ ¬Concurrent L M N := by
    idea "Use the 3 non-collinear points to build three lines, we can prove they're distinct with
    some RAA, and then use the lemma to do the rest."
    obtain ⟨A, B, C, hDistinct, hNC⟩ := ref axiom I.3
    rcases hDistinct with ⟨hAneB, hAneC, hBneC⟩
    obtain ⟨AB, ⟨hAonAB, hBonAB⟩, hABUniq⟩ := ref axiom I.1 A B hAneB
    obtain ⟨BC, ⟨hBonBC, hConBC⟩, hBCUniq⟩ := ref axiom I.1 B C hBneC
    obtain ⟨AC, ⟨hAonAC, hConAC⟩, hACUniq⟩ := ref axiom I.1 A C hAneC
    -- establish distinctness of lines
    have hABneBC : AB ≠ BC := by
      by_contra! hABeqBC
      have hCoffBC := hNC AB hAonAB hBonAB
      rw [hABeqBC] at hCoffBC
      contradiction
    have hABneAC : AB ≠ AC := by
      by_contra! hABeqAC
      have hCoffAC := hNC AB hAonAB hBonAB
      rw [hABeqAC] at hCoffAC
      contradiction
    have hBCneAC : BC ≠ AC := by
      by_contra! hBCeqAC
      rw [hBCeqAC] at hBonBC
      have hCoffAC := hNC AC hAonAC hBonBC
      contradiction
    -- Use our constructed apparatus
    use AB, BC, AC
    -- distinctness is already proven above
    constructor; trivial
    -- Now that everything is built, we proceed by contradiction
    by_contra! hNeg
    -- Let's find the Point the Author talks about in the proposed lemma
    obtain ⟨P, ⟨hPonAB, hPonBC, hPonAC⟩, hPUniq⟩ := ref lemma 1.0.26 ⟨hABneBC,hBCneAC,hABneAC⟩ hNeg
    -- This lemma was not suggested by the author, but is handy. The proof is not long and simply establishes the
    -- 'Parallel' fact for each pair of lines. We need the unique point and the negative condition to build
    -- these
    have hABnotparBC : (AB ∦ BC) := ref lemma 1.0.27 hPonAB hPonBC
    have hABnotparAC : (AB ∦ AC) := ref lemma 1.0.27 hPonAB hPonAC
    have hBCnotparAC : (BC ∦ AC) := ref lemma 1.0.27 hPonBC hPonAC
    idea "If P is on AB and BC, then P must be the intersection of those two lines, we already know B is on
    both AB and BC, and by P1, we know the intersection is unique, so P = B, but that means B is on AC, which
    which is false."
    -- We can use 2.1 to find the unique intersection, we mostly care about the uniqueness condition, not the
    -- incidence on.
    fixme "Note: Using the direct proof version of prop 2.1 since this predates the `.. intersects .. at ..` notation"
    obtain ⟨X, _, hXUniq⟩ := alternate 2.1 hABneBC hABnotparBC
    -- This condition makes proving this a matter of plug and chug
    have hPeqB : P = B := by
      have BeqX := hXUniq B ⟨hBonAB, hBonBC⟩
      have PeqX := hXUniq P ⟨hPonAB, hPonBC⟩
      rw [BeqX, PeqX]
    -- If P = B, the B on AC, since P on AC
    have hBonAC : B on AC := by
      rw [hPeqB] at hPonAC
      exact hPonAC
    -- Use Non-collinearity to show non-concurrence
    specialize hNC AC hAonAC hBonAC
    contradiction

attribute [simp] «Three distinct lines exist that are not concurrent»

end Geometry.Ch2.Prop
