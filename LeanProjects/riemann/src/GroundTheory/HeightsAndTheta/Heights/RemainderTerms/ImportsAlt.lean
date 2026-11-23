import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsComb
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Finset Comb

noncomputable section

theorem CombTableEqWords.proof (h1 : CombCardYoungCells.Statement)
    (h2 : CombWordOfTableau.Statement) (h3 : CombTableauOfWord.Statement) :
    CombTableEqWords.Statement := by
  intro m lam hlam
  classical
  let e : {T : youngCells lam ≃ Fin (youngCells lam).card // IsStandard T} ≃
      latticeWords (youngCells lam).card lam :=
    { toFun := fun T => ⟨rowWord T.1, (h2 m lam hlam T.1 T.2).1⟩
      invFun := fun w => ⟨Classical.choose (h3 m lam hlam w.1 w.2),
        (Classical.choose_spec (h3 m lam hlam w.1 w.2)).1⟩
      left_inv := by
        rintro ⟨T, hT⟩
        have hs := Classical.choose_spec (h3 m lam hlam (rowWord T) (h2 m lam hlam T hT).1)
        apply Subtype.ext
        have k1 := (h2 m lam hlam _ hs.1).2
        have k2 := (h2 m lam hlam T hT).2
        have hsymm : (Classical.choose
            (h3 m lam hlam (rowWord T) (h2 m lam hlam T hT).1)).symm = T.symm := by
          refine Equiv.ext fun t => Subtype.ext ?_
          rw [← k1 t, ← k2 t, hs.2]
        simpa using congrArg Equiv.symm hsymm
      right_inv := by
        rintro ⟨w, hw⟩
        exact Subtype.ext (Classical.choose_spec (h3 m lam hlam w hw)).2 }
  show Nat.card {T : youngCells lam ≃ Fin (youngCells lam).card // IsStandard T} = _
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe, h1 m lam]

end

end GroundTheory.Heights₂.Heights.RestTerms
