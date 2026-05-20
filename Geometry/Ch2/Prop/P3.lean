
import Geometry.Tactics

import Geometry.Theory.Axioms
import Atlas

open Geometry.Theory
open Atlas

namespace Geometry.Ch2.Prop

atlas commentary := by
  ref proposition 2.3
  page 71
  name "Every line has at least one point not on it"
  preface "For every line, there is at least one point not lying on it."

atlas proposition 2.3 "Every line has at least one point not on it"
  : ∀ L : Line, ∃ P : Point, (P off L) := by
      intro L
      by_contra! hNeg
      idea "There exist three non-colinear points, but if all points are on L (hNeg), then
      those points are colinear"
      have ⟨A,B,C, hDistinct, hNC⟩ := ref axiom I.3
      have AonL := hNeg A
      have BonL := hNeg B
      have ConL := hNeg C
      specialize hNC L AonL BonL
      contradiction


end Geometry.Ch2.Prop
