/-
Smoke test: `proof_figure` end-to-end.

Builds = the tactic ran on every example below without throwing. The
widget output isn't observable in a CLI build (only via LSP), but the
extract→lower→solve→SVG→parse pipeline executes here, so any failure
in those stages turns into a build error.
-/

import Geometry.Tactics.ProofFigure
import Geometry.Theory.Axioms
import Geometry.Theory.Distinct
import Geometry.Theory.Interpendices.B

namespace Geometry.Tests.ProofFigureSmoke

open Geometry.Theory

example (A B C : Point) (_h : A - B - C) : True := by
  proof_figure
  trivial

example (A B C D : Point) (_h₁ : A - B - C) (_h₂ : A - C - D) : True := by
  proof_figure
  trivial

example (A B C : Point) (_d : distinct A B C) : True := by
  proof_figure
  trivial

example (A B : Point) : True := by
  proof_figure
  trivial

end Geometry.Tests.ProofFigureSmoke
