import Geometry.Theory.Constructors
import Geometry.Theory.Distinct

namespace Geometry.Theory

-- p18 'Rays AB and AC are "opposite" if they are distinct, if they emanate from the same point A, and if they are part
-- of the same line AB = AC'
def OppositeRay (A B C : Point) : Prop :=
  (ray A B : Set Point) ≠ ray A C ∧ (line A B : Set Point) = line A C

syntax (name := oppositeRayNotation)
  "ray" ident ident "is" ("not")? "opposite" "ray" ident ident : term

macro_rules (kind := oppositeRayNotation)
  | `(ray $A:ident $B:ident is opposite ray $_:ident $C:ident) =>
      `(OppositeRay $A $B $C)
  | `(ray $A:ident $B:ident is not opposite ray $_:ident $C:ident) =>
      `(¬ OppositeRay $A $B $C)

@[app_unexpander OppositeRay]
def unexpandOppositeRay : Lean.PrettyPrinter.Unexpander
  | `($_ $A:ident $B:ident $C:ident) =>
      `(ray $A $B is opposite ray $A $C)
  | _ => throw ()

-- `Not (OppositeRay A B C)` shows as `ray A B is not opposite ray A C`
-- (uses the syntactic "not" word, not the `¬` prefix). Composes with
-- the OppositeRay unexpander above — by the time Not's unexpander runs,
-- the inner has already been rewritten to the ray-notation form, and
-- we just inject "not" before "opposite".
@[app_unexpander Not]
def unexpandNotOppositeRay : Lean.PrettyPrinter.Unexpander
  | `($_ $inner) =>
    match inner with
    | `(ray $A:ident $B:ident is opposite ray $C:ident $D:ident) =>
        `(ray $A $B is not opposite ray $C $D)
    | _ => throw ()
  | _ => throw ()

-- p18, 'An "angle with vertex A" is a point A together with distinct, non-opposite rays AB and AC (called the _sides_
-- of the angle) emanating from A (see figure 1.7)[^9]
--
-- We use the notation ∠ A, ∠ BAC, or ∠ CAB for this angle. If r = ray A B and s = ray A C, then rays r, s are said to
-- be coterminal (meaning they emanate from the same vertex), and the angle is also denoted ∠(r, s).
--
-- [footnote 9] According to this definition, there is no such thing in our treatment as a "straight angle", nor is
-- there such a thing as a "zero angle." We eliminated those expressions because most of the assertions we will make
-- about angles do not apply to them.'
def Angle (A B C : Point) : Prop :=
  (ray A B : Set Point) ≠ ray A C ∧ ray A B is not opposite ray A C

-- `∠ B A C` reads as Greenberg writes it: the middle letter is the vertex.
-- The def has vertex first, so the macro extracts the middle and reorders.
syntax (name := angleNotation) "∠" ident ident ident : term

macro_rules (kind := angleNotation)
  | `(∠ $X:ident $V:ident $Z:ident) => `(Angle $V $X $Z)

-- `Angle V X Z` → `∠ X V Z`: vertex (first arg of the def) becomes
-- the middle letter, per Greenberg's convention.
@[app_unexpander Angle]
def unexpandAngle : Lean.PrettyPrinter.Unexpander
  | `($_ $V:ident $X:ident $Z:ident) => `(∠ $X $V $Z)
  | _ => throw ()

-- FIXME: Author's def vs mine + quote here.
def Coterminal (A B C : Point) : Prop :=
  ray A B is not opposite ray A C ∧ (ray A B : Set Point) ≠ ray A C

syntax (name := coterminalNotation)
  "ray" ident ident "coterminal" "with" "ray" ident ident : term

macro_rules (kind := coterminalNotation)
  | `(ray $A:ident $B:ident coterminal with ray $_:ident $C:ident) =>
      `(Coterminal $A $B $C)

@[app_unexpander Coterminal]
def unexpandCoterminal : Lean.PrettyPrinter.Unexpander
  | `($_ $A:ident $B:ident $C:ident) =>
      `(ray $A $B coterminal with ray $A $C)
  | _ => throw ()

end Geometry.Theory
