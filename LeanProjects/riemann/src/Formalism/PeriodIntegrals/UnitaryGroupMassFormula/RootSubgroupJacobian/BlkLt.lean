import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RootSubgroupBasics.NegOnePowMulSelf

noncomputable section

namespace PI.AmpRootJacW

open Formalism.MainNotions.S PI.AmpRootCommon

theorem blk_lt : ∀ (bs : List (ℂ × ℕ)) (i j : ℕ), i < j → j < (bs.map Prod.snd).sum →
    blockIdx bs i ≠ blockIdx bs j → pv bs i < pv bs j
  | [], i, j, _, hj, _ => by simp at hj
  | (t, s) :: bs, i, j, hij, hj, hne => by
    simp only [List.map_cons, List.sum_cons] at hj
    simp only [blockIdx, pv] at hne ⊢
    by_cases hi : i < s
    · by_cases hjs : j < s
      · simp [hi, hjs] at hne
      · rw [if_pos hi, if_neg hjs]; omega
    · have hjs : ¬ j < s := by omega
      rw [if_neg hi, if_neg hjs] at hne ⊢
      have := blk_lt bs (i - s) (j - s) (by omega) (by omega) (fun e => hne (by rw [e]))
      omega

end PI.AmpRootJacW
