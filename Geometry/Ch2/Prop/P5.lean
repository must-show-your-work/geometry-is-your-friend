import Geometry.Tactics

import Geometry.Theory.Axioms
import Geometry.Theory.Ch1
import Geometry.Theory.Point.Ch1
import Geometry.Theory.Line.Ch1
import Atlas

import Geometry.Ch2.Prop.P2
import Geometry.Ch2.Prop.P3

namespace Geometry.Ch2.Prop

open Geometry.Theory
open Atlas


atlas commentary := by
  ref proposition 2.5
  page 71
  name "Every point has at least two distinct lines through it"
  preface "For every point P, there are at least two distinct lines through P"

atlas proposition 2.5 "Every point has at least two distinct lines through it"
  : ∀ P : Point, ∃ L M : Line,
    L ≠ M ∧ (P on L) ∧ (P on M) := by
        intro P
        have ⟨Q, PneQ⟩ := ref lemma 1.0.11 P
        have ⟨PQ, _⟩ := ref axiom I.1 P Q PneQ
        idea "We have an arbitrary ray PQ, by P2.3 there is a point R not on it."
        obtain ⟨R, RoffPQ⟩ := proposition 2.3 PQ
        comment "Since PQ avoids R, P ≠ R"
        have PneR : P ≠ R := by
            by_contra! hNeg
            rw [<- hNeg] at RoffPQ
            obvious
        comment "So we have PR ≠ PQ"
        obtain ⟨PR, ⟨PonPR, RonPR⟩, PRuniq⟩ := ref axiom I.1 P R PneR
        use PQ, PR
        have PQnePR : PQ ≠ PR := by
            rw [ref lemma 1.0.29]
            use R; obvious
        obvious



end Geometry.Ch2.Prop
