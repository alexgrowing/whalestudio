import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsRest
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Finset

theorem flagIntegral_sum {ι : Type*} (f N : ℕ) (s : Finset ι)
    (P : ι → RestTerms.RootRing f N) :
    RestTerms.flagIntegral f N (∑ i ∈ s, P i) = ∑ i ∈ s, RestTerms.flagIntegral f N (P i) := by
  unfold RestTerms.flagIntegral
  simp only [coeff_sum, Finset.sum_mul]
  exact Finset.sum_comm

theorem RestCutFlagKillsIdeal.proof (h₁ : RestTerms.FlagIntegralKillsPowerSums.Statement)
    (h₂ : RestCutIdealSum.Statement) : RestCutFlagKillsIdeal.Statement := by
  intro f N A hA
  obtain ⟨G, rfl⟩ := h₂ f N A hA
  rw [flagIntegral_sum]
  refine Finset.sum_eq_zero fun i _ => h₁ f N ((i.1 : ℕ) + 1) i.2 (G i) (by omega) ?_
  have := i.1.isLt
  omega

end GroundTheory.Heights₂.Heights
