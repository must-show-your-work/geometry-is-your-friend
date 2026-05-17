import Geometry.Tactics

import Geometry.Theory.Axioms
import Geometry.Ch2.Prop.P2
import Atlas

namespace Geometry.Ch2.Prop

open Geometry.Theory

/-- p71. "For every point, there is at least one line not passing through it." -/
atlas proposition 2.4 "Every point has at least one line not through it"
  (P : Point) : ∃ L : Line, (P off L) := by
    -- Similar to 2.3, but using 2.2's configuration.
    obtain ⟨L, M, N, hDistinct, hNC⟩ := Geometry.Ch2.Prop.P2
    unfold Concurrent at hNC
    by_contra! hNeg
    push_neg at *
    specialize hNC P
    have PonN := hNeg N
    have PoffN := hNC (hNeg L) (hNeg M)
    contradiction

alias P4 := «Every point has at least one line not through it»

end Geometry.Ch2.Prop
