import Geometry.Tactics
import Geometry.Theory.Axioms
import Geometry.Construction.AtlasField
import Atlas

namespace Geometry.Ch2.Prop

open Set
open Geometry.Theory
open Atlas

atlas commentary := by
  via alternate 2.1
  page 71
  name "Distinct non-parallel lines share a unique point (direct proof)"
  preface "If `l` and `m` are distinct lines that are not parallel, then `l` and `m` have a unique point in common"

  -- figure := by
    -- construction {
      -- exists X : Point
      -- exists L M : Line
      -- assert incident X L
      -- assert incident X M
    -- }
    -- title "Proposition 2.1 (direct)"
    -- index 1
    -- caption "Two distinct non-parallel lines L and M meet at the unique point X."

atlas alternate 2.1 "Distinct non-parallel lines share a unique point (direct proof)"
  {L M : Line} :
  L ≠ M → (L ∦ M) → ∃! P : Point,
     (P on L) ∧ (P on M)
:= by
    intro hDistinctLines
    unfold Parallel; push Not
    intro hypP; specialize hypP hDistinctLines
    obtain ⟨P, hPonLM⟩ := hypP
    refine ⟨P, ?cEx, ?cUniq⟩
    -- existence
    exact hPonLM
    -- uniqueness
    intro Q
    by_contra! ⟨hQonLM, hNeg⟩
    idea "PQ = L, PQ = M, but L != M"
    obtain ⟨PQ, _, hPQUniq⟩ := via axiom I.1 P Q hNeg.symm
    have hLisPQ := hPQUniq L ⟨hPonLM.left, hQonLM.left⟩
    have hMisPQ := hPQUniq M ⟨hPonLM.right, hQonLM.right⟩
    have hLeqM : (L = M) := by
        rw [hMisPQ, hLisPQ]
    contradiction

atlas commentary := by
  via proposition 2.1
  name "Distinct non-parallel lines share a unique point"
  preface "A corrolary of the main theorem that is more useful since it uses the syntax directly."

  -- figure := by
    -- construction {
      -- exists X : Point
      -- exists L M : Line
      -- assert incident X L
      -- assert incident X M
    -- }
    -- title "Proposition 2.1"
    -- index 1
    -- caption "Distinct non-parallel lines meet at exactly one point."

atlas proposition 2.1 "Distinct non-parallel lines share a unique point"
  (LneM : L ≠ M) (LnoparM : L ∦ M) : ∃! X : Point, L intersects M at X := by
    obtain ⟨P, ⟨PonL, PonM⟩, Puniq⟩ := alternate 2.1 LneM LnoparM
    use P
    constructor
    · unfold Intersects
      apply Line.ext_set
      apply Subset.antisymm
      · intro Q QinInt
        rw [Line.inter_toSet] at QinInt
        have ⟨QonL, QonM⟩ := QinInt
        specialize Puniq Q ⟨QonL, QonM⟩
        rw [Puniq]
        rw [Line.singleton_toSet]; obvious
      · intro Q QinSingle
        rw [Line.singleton_toSet] at QinSingle
        have QeqP : Q = P := by obvious
        rw [Line.inter_toSet]; rw [QeqP]
        obvious
    · intro Q LintMatQ
      unfold Intersects at LintMatQ
      specialize Puniq Q
      have QinLintM : Q ∈ L ∩ M := by rw [LintMatQ]; simp
      obvious

end Geometry.Ch2.Prop
