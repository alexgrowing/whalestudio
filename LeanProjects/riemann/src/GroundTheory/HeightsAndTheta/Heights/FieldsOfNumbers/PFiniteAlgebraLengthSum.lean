import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsFiniteAlgebraLengthSum
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.LengthSumLocalizations
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open Module

theorem FiniteAlgebraLengthSum.proof : FiniteAlgebraLengthSum.Statement := by
  classical
  intro A B _ _ _ _ _ ι _ 𝔪 h𝔪 hinj hall C _ _ hC α
  have : ∀ i, (𝔪 i).IsMaximal := h𝔪
  have : ∀ i, IsLocalization.AtPrime (C i) (𝔪 i) := hC
  have hrange : LinearMap.range (LinearMap.lsmul A B α) =
      (Ideal.span {algebraMap A B α}).restrictScalars A := by
    ext b
    simp only [LinearMap.mem_range, LinearMap.lsmul_apply, Submodule.restrictScalars_mem,
      Ideal.mem_span_singleton', Algebra.smul_def, mul_comm]
  rw [(Submodule.quotEquivOfEq _ _ hrange).length_eq,
    (Submodule.Quotient.restrictScalarsEquiv A (Ideal.span {algebraMap A B α})).length_eq,
    LengthSumLocalizations.length_eq_sum 𝔪 C hinj hall A]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Ring.ord, ← (Algebra.TensorProduct.quotIdealMapEquivTensorQuot (C i)
    (Ideal.span {algebraMap A B α})).toLinearEquiv.length_eq, Ideal.map_span, Set.image_singleton]

end GroundTheory.Heights₂.Heights.FieldNumbers
