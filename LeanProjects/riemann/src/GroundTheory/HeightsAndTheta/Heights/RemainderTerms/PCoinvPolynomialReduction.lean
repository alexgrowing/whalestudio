import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsCoinv
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset Coinv

noncomputable section

theorem CoinvPolynomialReduction.proof (h1 : CoinvMonomialReduction.Statement) :
    CoinvPolynomialReduction.Statement := by
  intro K _ _ f n H
  choose v hv hvI using fun d => h1 K f n d
  refine ⟨∑ d ∈ H.support, coeff d H • v d, ?_, ?_⟩
  · exact Submodule.sum_mem _ fun d _ => Submodule.smul_mem _ _ (hv d)
  · have e1 : H - ∑ d ∈ H.support, coeff d H • v d =
        (∑ d ∈ H.support, monomial d (coeff d H)) - ∑ d ∈ H.support, coeff d H • v d := by
      rw [← H.as_sum]
    have e2 : (∑ d ∈ H.support, monomial d (coeff d H)) - ∑ d ∈ H.support, coeff d H • v d =
        ∑ d ∈ H.support, C (coeff d H) * (monomial d (1 : K) - v d) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [mul_sub, C_mul_monomial, mul_one, smul_eq_C_mul]
    rw [e1, e2]
    exact Ideal.sum_mem _ fun d _ => Ideal.mul_mem_left _ _ (hvI d)

end

end GroundTheory.Heights₂.Heights.RestTerms
