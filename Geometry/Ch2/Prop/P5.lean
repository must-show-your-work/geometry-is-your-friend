import Geometry.Tactics

import Geometry.Theory.Axioms
import Geometry.Theory.Interpendices.A

import Geometry.Ch2.Prop.P3

import Geometry.Construction.AtlasField
import Atlas

namespace Geometry.Ch2.Prop

open Geometry.Theory
open Atlas


atlas commentary := by
  via proposition 2.5
  page 71
  name "Every point has at least two distinct lines through it"
  preface "For every point P, there are at least two distinct lines through P"

  figure := by
    construction {
      exists P : Point
      exists L M : Line
      assert incident P L
      assert incident P M
    }
    title "Proposition 2.5"
    index 1
    caption "Through any P there pass at least two distinct lines L and M."

atlas proposition 2.5 "Every point has at least two distinct lines through it"
  : ∀ P : Point, ∃ L M : Line,
    L ≠ M ∧ (P on L) ∧ (P on M) := by
        intro P
        have ⟨Q, PneQ⟩ := via lemma 1.0.4 P
        have ⟨PQ, _⟩ := via axiom I.1 P Q PneQ
        idea "We have an arbitrary ray PQ, by P2.3 there is a point R not on it."
        obtain ⟨R, RoffPQ⟩ := proposition 2.3 PQ
        comment "Since PQ avoids R, P ≠ R"
        have PneR : P ≠ R := by
            by_contra! hNeg
            rw [<- hNeg] at RoffPQ
            obvious
        comment "So we have PR ≠ PQ"
        obtain ⟨PR, ⟨PonPR, RonPR⟩, PRuniq⟩ := via axiom I.1 P R PneR
        use PQ, PR
        have PQnePR : PQ ≠ PR := by
            rw [via lemma 1.0.11]
            use R; obvious
        obvious



end Geometry.Ch2.Prop
