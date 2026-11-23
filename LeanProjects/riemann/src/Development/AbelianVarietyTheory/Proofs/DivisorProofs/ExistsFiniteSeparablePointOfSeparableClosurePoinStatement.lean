import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteSeparablePointOfSeparableClosurePoin
import Mathlib
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_separable_point_of_separableClosure_point' : ∀ (k B : Type) [Field k] [CommRing B] [Algebra k B], Algebra.FiniteType k B → Nonempty (B →ₐ[k] SeparableClosure k) → ∃ (k' : Type) (_ : Field k') (_ : Algebra k k'), FiniteDimensional k k' ∧ Algebra.IsSeparable k k' ∧ Nonempty (B →ₐ[k] k') := by
  first | exact @GlobalTheory.exists_finite_separable_point_of_separableClosure_point | exact GlobalTheory.exists_finite_separable_point_of_separableClosure_point | (intros; apply GlobalTheory.exists_finite_separable_point_of_separableClosure_point <;> assumption)
