import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsFlag
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PHomogeneousComponentMul
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

noncomputable section

theorem FlagQuotientHomogeneous.proof : FlagQuotientHomogeneous.Statement := by
  intro σ A R m k hA0 hA hAR
  have hzero : ∀ j, j ≠ k → homogeneousComponent j R = 0 := by
    intro j hj
    have h1 := HomogeneousComponentMul.proof σ ℚ A R m (m + j) hA
    rw [if_pos (Nat.le_add_right m j), Nat.add_sub_cancel_left] at h1
    have h2 : homogeneousComponent (m + j) (A * R) = 0 := by
      rw [homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).mpr hAR),
        if_neg (by omega)]
    rw [h2] at h1
    exact (mul_eq_zero.mp h1.symm).resolve_left hA0
  have hR : R = homogeneousComponent k R := by
    conv_lhs => rw [← sum_homogeneousComponent R]
    refine Finset.sum_eq_single k (fun j _ hj => hzero j hj) (fun hk => ?_)
    rw [Finset.mem_range, not_lt] at hk
    exact homogeneousComponent_eq_zero k R (by omega)
  rw [hR]
  exact homogeneousComponent_isHomogeneous k R

end

end GroundTheory.Heights₂.Heights.RestTerms
