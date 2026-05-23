import Geometry.Tactics

import Geometry.Theory.Axioms
import Geometry.Ch2.Prop.P2
import Atlas

namespace Geometry.Ch2.Prop

open Geometry.Theory
open Atlas

atlas commentary := by
  ref proposition 2.4
  page 71
  name "Every point has at least one line not through it"
  preface "For every point, there is at least one line not passing through it."

atlas proposition 2.4 "Every point has at least one line not through it"
  (P : Point) : ∃ L : Line, (P off L) := by
    comment "Similar to 2.3, but using 2.2's configuration."
    obtain ⟨L, M, N, hDistinct, hNC⟩ := proposition 2.2
    unfold Concurrent at hNC
    by_contra! hNeg
    push Not at *
    specialize hNC P
    have PonN := hNeg N
    have PoffN := hNC (hNeg L) (hNeg M)
    contradiction


end Geometry.Ch2.Prop
