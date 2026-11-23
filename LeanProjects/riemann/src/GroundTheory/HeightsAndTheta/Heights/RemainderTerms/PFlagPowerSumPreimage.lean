import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Statements
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PowerSums
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsFlag
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial Finset

noncomputable section

theorem sum_Icc_one_eq_sum_fin {M : Type*} [AddCommMonoid M] (N : ℕ) (g : ℕ → M) :
    ∑ l ∈ Finset.Icc 1 N, g l = ∑ i : Fin N, g (i.val + 1) := by
  have hI : Finset.Icc 1 N = Finset.Ico 1 (N + 1) := by
    ext l
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [Fin.sum_univ_eq_sum_range (fun i => g (i + 1)), hI, Finset.sum_Ico_eq_sum_range,
    Nat.add_sub_cancel]
  exact Finset.sum_congr rfl (fun i _ => by rw [add_comm])

theorem FlagPowerSumPreimage.proof : FlagPowerSumPreimage.Statement := by
  intro N T hT
  choose Sf hSf using fun l => Flag.exists_powerSumHom_eq (hT l)
  refine ⟨∑ i : Fin N, X i * Sf (i.val + 1), ?_, ?_⟩
  · rw [sum_Icc_one_eq_sum_fin N (fun l => psum (Fin N) ℚ l * T l), map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_mul, hSf]
    simp [powerSumHom]
  · intro k hk1 hkN
    set j : Fin N := ⟨k - 1, by omega⟩ with hj
    rw [coeff_sum, Finset.sum_eq_single j]
    · rw [coeff_X_mul', if_pos (by simp), tsub_self, ← constantCoeff_eq,
        ← Flag.constantCoeff_powerSumHom, hSf]
      have : j.val + 1 = k := by simp [hj]; omega
      rw [this]
    · intro i _ hij
      rw [coeff_X_mul', if_neg]
      simp only [Finsupp.mem_support_iff, ne_eq]
      rw [Finsupp.single_apply, if_neg (fun h => hij h.symm)]
      simp
    · intro h
      exact absurd (Finset.mem_univ j) h

end

end RestTerms

end GroundTheory.Heights₂.Heights
