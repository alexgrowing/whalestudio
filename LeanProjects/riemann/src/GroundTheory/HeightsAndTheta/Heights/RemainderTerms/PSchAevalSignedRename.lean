import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Statements
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsSchur
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

noncomputable section

theorem SchAevalSignedRename.proof : SchAevalSignedRename.Statement := by
  intro ι κ _ _ _ _ s g d P hP
  conv_lhs => rw [P.as_sum]
  conv_rhs => rw [P.as_sum]
  rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e he => ?_
  have hd : (∑ i ∈ e.support, e i) = d := by
    have h := hP (mem_support_iff.mp he)
    simpa [Finsupp.weight_apply, Finsupp.sum] using h
  rw [rename_monomial, aeval_monomial, monomial_eq, Finsupp.prod_mapDomain_index
    (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]
  simp only [algebraMap_eq, Finsupp.prod, mul_pow, Finset.prod_mul_distrib,
    ← C_pow]
  rw [← map_prod, Finset.prod_pow_eq_pow_sum, hd]
  ring

end

end GroundTheory.Heights₂.Heights.RestTerms
