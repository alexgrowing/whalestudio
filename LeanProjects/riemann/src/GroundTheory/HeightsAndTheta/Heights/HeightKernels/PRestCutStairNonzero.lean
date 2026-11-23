import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsRest
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem flagIntegral_sub_C_mul (f N : ℕ) (H S : RestTerms.RootRing f N) (b : ℚ) :
    RestTerms.flagIntegral f N (H - C b * S) =
      RestTerms.flagIntegral f N H - b * RestTerms.flagIntegral f N S := by
  unfold RestTerms.flagIntegral
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [coeff_sub, coeff_C_mul]
  ring

theorem RestCutStairNonzero.proof (h₁ : RestTerms.CoinvariantTopDegree.Statement)
    (h₂ : RestCutFlagKillsIdeal.Statement) : RestCutStairNonzero.Statement := by
  intro f N H hH hne hstair
  obtain ⟨b, hb⟩ := h₁ f N H hH
  have hmem : H - C b * restStair f N ∈ restPsumIdeal f N := hb
  have h0 := h₂ f N _ hmem
  rw [flagIntegral_sub_C_mul, hstair, mul_zero, sub_zero] at h0
  exact hne h0

end GroundTheory.Heights₂.Heights
