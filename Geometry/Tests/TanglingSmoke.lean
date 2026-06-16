import Geometry.Theory.Tangling

namespace Geometry.Tests.TanglingSmoke

open Geometry.Theory

noncomputable example (A B : Point) (h : Collinear ({A, B} : Finset Point)) :
    Tangling := { points := {A, B}, col := h, known := ∅ }

noncomputable example (A B C : Point) (h : Collinear ({A, B, C} : Finset Point))
    (ABC : A - B - C) : Tangling :=
  let t : Tangling := { points := {A, B, C}, col := h, known := ∅ }
  t.addBetween (by aesop) (by aesop) (by aesop) ABC

end Geometry.Tests.TanglingSmoke
