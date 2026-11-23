import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsEqConstMulOfForallExistsNormEq
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.EqZeroOfMulEqZero
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_eq_const_mul_of_forall_exists_norm_eq' : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (ι : Type) [Countable ι] (O : Set V), IsOpen O → IsPreconnected O → O.Nonempty → ∀ (P : V → ℂ) (Q : ι → V → ℂ), DifferentiableOn ℂ P O → (∀ i, DifferentiableOn ℂ (Q i) O) → (∀ x ∈ O, ∃ i, ‖P x‖ = ‖Q i x‖) → ∃ (i : ι) (c : ℂ), ∀ x ∈ O, P x = c * Q i x := by
  first | exact @GlobalTheory.exists_eq_const_mul_of_forall_exists_norm_eq | exact GlobalTheory.exists_eq_const_mul_of_forall_exists_norm_eq | (intros; apply GlobalTheory.exists_eq_const_mul_of_forall_exists_norm_eq <;> assumption)
