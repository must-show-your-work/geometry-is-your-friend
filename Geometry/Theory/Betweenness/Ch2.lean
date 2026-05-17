import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Insert
import Geometry.Theory.Axioms
import Geometry.Theory.Ch1
import Geometry.Theory.Line.Ch1
import Geometry.Theory.Line.Ch2
import Geometry.Tactics
import Atlas

namespace Geometry.Theory

open Set
open Geometry.Theory

namespace Betweenness

-- TODO: For this and other commutative properties, I think there is a class to instantiate to get that .symm thing to
-- work.

/-- a line doesn't care about the order of the points it guards -/
atlas lemma 2.0.30 "Guarding is symmetric in its two point arguments"
  : (L guards A and B) -> (L guards B and A) := by
    intro LguardsAB
    unfold SameSide at *; rw [<- ref lemma 2.0.13] ; tauto


/-- a line doesn't care about the order of the points it splits -/
atlas lemma 2.0.31 "Splitting is symmetric in its two point arguments"
  : (L splits A and B) -> (L splits B and A) := by
    intro LsplitsAB
    unfold SameSide at *; rw [<- ref lemma 2.0.13] ; tauto



end Betweenness

end Geometry.Theory
