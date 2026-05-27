import Mathlib.Data.List.Basic
import Geometry.Theory.Axioms
import Geometry.Theory.Interpendices.A
import Geometry.Tactics

import Geometry.Ch3.Prop.P3
import Geometry.Ch3.Ex.Ex1

import Atlas

namespace Geometry.Theory

open Geometry.Ch3.Prop
open Geometry.Ch3.Ex
open Atlas

atlas commentary := by
  ref lemma 3.0.3
  name "Four-point arrangement from two overlapping outer-pair triples"
  preface "Given A - B - C and A - C - D, the four ordered triples of [A, B, C, D] are: A-B-C and A-C-D (inputs); B-C-D (Prop 3.3.i); A-B-D (Prop 3.3.ii)."

atlas lemma 3.0.3 "Four-point arrangement from two overlapping outer-pair triples"
  {A B C D : Point} (h₁ : A - B - C) (h₂ : A - C - D) : Arrangement [A, B, C, D] := by
  have h₃ : B - C - D := via proposition 3.3.i ⟨h₁, h₂⟩
  have h₄ : A - B - D := via proposition 3.3.ii ⟨h₁, h₂⟩
  refine ⟨by simp, ?_⟩
  intro i j k hij hjk
  rcases i with ⟨i, hi⟩
  rcases j with ⟨j, hj⟩
  rcases k with ⟨k, hk⟩
  simp only [show ([A, B, C, D] : List Point).length = 4 from rfl] at hi hj hk
  have hij : i < j := hij
  have hjk : j < k := hjk
  rcases Nat.lt_or_ge j 2 with hj' | hj'
  · obtain rfl : j = 1 := by omega
    obtain rfl : i = 0 := by omega
    rcases Nat.lt_or_ge k 3 with hk' | hk'
    · obtain rfl : k = 2 := by omega
      exact h₁
    · obtain rfl : k = 3 := by omega
      exact h₄
  · obtain rfl : j = 2 := by omega
    obtain rfl : k = 3 := by omega
    rcases Nat.lt_or_ge i 1 with hi' | hi'
    · obtain rfl : i = 0 := by omega
      exact h₂
    · obtain rfl : i = 1 := by omega
      exact h₃

end Geometry.Theory
