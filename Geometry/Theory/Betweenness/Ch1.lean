import Geometry.Theory.Interpendices.A

/-!
Re-export shim during the interpendix migration. Original contents
(`lemma 1.0.36`, `1.0.37`, `1.0.38`) have moved to
`Geometry/Theory/Interpendices/A.lean` (axiom-only-derivable).

This shim keeps existing import paths working until the migration is
complete; delete once all consumers import the interpendices directly.
-/
