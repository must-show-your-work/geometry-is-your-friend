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


/-- p71. "For every point P, there are at least two distinct lines through P" -/
atlas proposition 2.5 "Every point has at least two distinct lines through it"
  : ∀ P : Point, ∃ L M : Line,
    L ≠ M ∧ (P on L) ∧ (P on M) := by
        intro P
        have ⟨Q, PneQ⟩ := Point.distinct_points_exist P
        have ⟨PQ, _⟩ := I1 P Q PneQ
        -- So we have an arbitrary ray PQ, by P2.3 there is a point R not on it.
        obtain ⟨R, RoffPQ⟩ := Geometry.Ch2.Prop.P3 PQ
        -- Since PQ avoids R, P ≠ R
        have PneR : P ≠ R := by
            by_contra! hNeg
            rw [<- hNeg] at RoffPQ
            tauto
        -- So we have PR ≠ PQ
        obtain ⟨PR, ⟨PonPR, RonPR⟩, PRuniq⟩ := I1 P R PneR
        -- Let's stake our claim
        use PQ, PR
        have PQnePR : PQ ≠ PR := by
            rw [Line.distinguishing_point]
            use R; tauto
        /- without the corollary, this is a few lines longer.
        -- 5.2.1 should have a much better proof, I just don't know enough lean to do it.
        have PQnePR : PQ ≠ PR := by
            by_contra! hNeg
            rw [P5.L2] at hNeg
            specialize hNeg R
            tauto -/
        -- trivial fromn here
        tauto


alias P5 := «Every point has at least two distinct lines through it»

end Geometry.Ch2.Prop
