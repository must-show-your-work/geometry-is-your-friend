import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Insert
import Geometry.Theory.Axioms
import Geometry.Tactics
import Atlas

namespace Geometry.Theory

open Set
open Geometry.Theory

namespace Betweenness

/-- With respect to a fixed point, every pair of points can be said to either be 'to the left' or 'to the right' of
one another -/
atlas lemma 1.0.36 "Betweenness contradiction: A-B-C cannot coexist with B-A-C"
  : A - B - C ∧ B - A - C -> False := by
  intro ⟨ABC, _⟩
  obtain ⟨distinctABC, colABC⟩ := ref axiom B-1a ABC
  rcases ref axiom B.3 A B C ⟨distinctABC, colABC⟩ with ⟨ABC, nBAC, nACB⟩ | ⟨nABC,BAC,nACB⟩ | ⟨nABC,nBAC,ACB⟩
  repeat contradiction


/-- With respect to a fixed point, every pair of points can be said to either be 'to the left' or 'to the right' of
one another -/
atlas lemma 1.0.37 "Betweenness contradiction: A-B-C cannot coexist with A-C-B"
  : A - B - C ∧ A - C - B -> False := by
  intro ⟨ABC, _⟩
  obtain ⟨distinctABC, colABC⟩ := ref axiom B-1a ABC
  rcases ref axiom B.3 A B C ⟨distinctABC, colABC⟩ with ⟨ABC, nBAC, nACB⟩ | ⟨nABC,BAC,nACB⟩ | ⟨nABC,nBAC,ACB⟩
  repeat contradiction


/-- With respect to a pair of fixed points, another point is either 'to the left' or 'to the right' of the pair -/
atlas lemma 1.0.38 "Betweenness contradiction: A-B-C cannot coexist with C-A-B"
  : A - B - C ∧ C - A - B -> False := by
  intro ⟨ABC, _⟩
  obtain ⟨distinctABC, colABC⟩ := ref axiom B-1a ABC
  rcases ref axiom B.3 A B C ⟨distinctABC, colABC⟩ with ⟨ABC, nBAC, nACB⟩ | ⟨nABC,BAC,nACB⟩ | ⟨nABC,nBAC,ACB⟩
  rw [ref axiom B-1b] at nBAC;
  repeat contradiction


-- TODO: use the `distinct` condition here
/-- betweeness implies distinctness -/
atlas lemma 1.0.39 "Betweenness A-B-C implies the three points are distinct"
  : A - B - C -> distinct A B C := by
  intro ABC
  have ⟨h,  _⟩ := (ref axiom B-1a ABC)
  exact h


/-- betweeness implies collinearity -/
atlas lemma 1.0.40 "Betweenness A-B-C implies the three points are collinear"
  : A - B - C -> collinear A B C := by
  intro ABC
  exact (ref axiom B-1a ABC).right

  
end Betweenness

end Geometry.Theory
