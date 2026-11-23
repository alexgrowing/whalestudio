import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Statements
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsFlag
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial Finset

theorem FlagIntegralTopComponent.proof (h1 : FlagVandermondeHomogeneous.Statement) :
    FlagIntegralTopComponent.Statement := by
  intro f N Φ
  unfold flagIntegral
  refine Finset.sum_congr rfl fun α hα => ?_
  have hdeg : α.degree = topDegree f N := by
    rw [Finsupp.degree_eq_weight_one]
    exact h1 f N (mem_support_iff.mp hα)
  rw [coeff_homogeneousComponent, if_pos hdeg]

end RestTerms

end GroundTheory.Heights₂.Heights
