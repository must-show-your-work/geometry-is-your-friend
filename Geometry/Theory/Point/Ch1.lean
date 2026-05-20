import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Insert
import Geometry.Theory.Axioms
import Geometry.Tactics
import Atlas

namespace Geometry.Theory

open Set
open Geometry.Theory
open Atlas

namespace Point

atlas commentary := by
  ref lemma 1.0.11
  name "For every Point there exists at least one distinct Point"
  preface "For every Point, there is at least one point that isn't that point."

atlas lemma 1.0.11 "For every Point there exists at least one distinct Point"
  : ∀ P : Point, ∃ Q : Point, P ≠ Q := by
    intro P
    obtain ⟨A, B, C, hDistinct, _⟩ := ref axiom I.3
    idea "There is a configuration of 3 non-colinear points. Either P is one of those points, or it's none of
    them. If it's one of them, there are two other points distinct from P; if it's not one of them, then
    there are three distinct points."
    by_cases hSupposePeqA : P = A -- ∨ P = B ∨ P = C
    rw [<- hSupposePeqA] at hDistinct
    use B
    exact hDistinct.left
    use A



end Point

end Geometry.Theory
