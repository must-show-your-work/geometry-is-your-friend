/-
Smoke test for the top-level `Atlas` module. Defines a trivial
proposition via the macro and references it via both the elab term and
the French-quoted title to exercise the full pipeline (macro → attribute
→ env extension → reference lookup).

Delete or extend as the real migration progresses.
-/

import Atlas

namespace AtlasTest

atlas proposition 0.1 "Reflexivity of Equality on Nat"
    : ∀ n : Nat, n = n := by intro _; rfl

-- Reference by elab term:
example : ∀ n : Nat, n = n := proposition 0.1

-- Reference by French-quoted title:
example : ∀ n : Nat, n = n := «Reflexivity of Equality on Nat»

-- Binder pass-through — `{n : Nat}` and `(h : ...)` survive the macro.
atlas lemma 0.2 "Equality is symmetric for Nat"
    {a b : Nat} (h : a = b) : b = a := by rw [h]

example {x y : Nat} (heq : x = y) : y = x := lemma 0.2 heq

-- Mixed positional + implicit binders, def kind.
atlas definition 0.3 "Square of a Nat" (n : Nat) : Nat := n * n

#eval definition 0.3 7  -- expects 49

-- Un-numbered form: theory-style lemma with no book reference.
atlas lemma "Addition associativity (Nat)"
    (a b c : Nat) : a + b + c = a + (b + c) := by ac_rfl

#check «Addition associativity (Nat)»

end AtlasTest
