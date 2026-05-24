import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Insert
import Geometry.Theory.Axioms
import Geometry.Tactics
import Atlas

namespace Geometry.Theory

open Set
open Geometry.Theory
open Atlas

namespace Betweenness

atlas commentary := by
  ref lemma 1.0.36
  name "Betweenness contradiction: A-B-C cannot coexist with B-A-C"
  preface "With respect to a fixed point, every pair of points can be said to either be 'to the left' or 'to the right' of
one another"

atlas lemma 1.0.36 "Betweenness contradiction: A-B-C cannot coexist with B-A-C"
  : A - B - C ∧ B - A - C -> False := by
  intro ⟨ABC, _⟩
  obtain ⟨distinctABC, colABC, _⟩ := ref axiom B.1 ABC
  rcases ref axiom B.3 A B C ⟨distinctABC, colABC⟩ with ⟨ABC, nBAC, nACB⟩ | ⟨nABC,BAC,nACB⟩ | ⟨nABC,nBAC,ACB⟩
  repeat contradiction


atlas commentary := by
  ref lemma 1.0.37
  name "Betweenness contradiction: A-B-C cannot coexist with A-C-B"
  preface "With respect to a fixed point, every pair of points can be said to either be 'to the left' or 'to the right' of
one another"

atlas lemma 1.0.37 "Betweenness contradiction: A-B-C cannot coexist with A-C-B"
  : A - B - C ∧ A - C - B -> False := by
  intro ⟨ABC, _⟩
  obtain ⟨distinctABC, colABC, _⟩ := ref axiom B.1 ABC
  rcases ref axiom B.3 A B C ⟨distinctABC, colABC⟩ with ⟨ABC, nBAC, nACB⟩ | ⟨nABC,BAC,nACB⟩ | ⟨nABC,nBAC,ACB⟩
  repeat contradiction


atlas commentary := by
  ref lemma 1.0.38
  name "Betweenness contradiction: A-B-C cannot coexist with C-A-B"
  preface "With respect to a pair of fixed points, another point is either 'to the left' or 'to the right' of the pair"

atlas lemma 1.0.38 "Betweenness contradiction: A-B-C cannot coexist with C-A-B"
  : A - B - C ∧ C - A - B -> False := by
  intro ⟨ABC, CAB⟩
  obtain ⟨distinctABC, colABC, _⟩ := ref axiom B.1 ABC
  rcases ref axiom B.3 A B C ⟨distinctABC, colABC⟩ with ⟨_, nBAC, _⟩ | ⟨nABC, _, _⟩ | ⟨nABC, _, _⟩
  · exact nBAC CAB.symm
  · exact nABC ABC
  · exact nABC ABC

end Betweenness

end Geometry.Theory
