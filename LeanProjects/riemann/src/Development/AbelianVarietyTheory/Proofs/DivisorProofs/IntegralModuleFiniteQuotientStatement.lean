import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralModuleFiniteQuotient
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNilRad
open Matrix GlobalTheory.TorFin
open scoped ContDiff

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_module_finite_quotient : ∀ (A U W : Type) [Ring A] [Algebra ℂ A] [AddCommGroup U] [Module ℂ U] [AddCommGroup W] [Module ℂ W] (Z : Subalgebra ℂ A) (I : Submodule ℂ A) (H H' : A) (κ : A →ₗ[ℂ] U) (Λ : A →ₗ[ℂ] W), Commute H H' → (∀ i ∈ I, H * i ∈ I) → (∀ i ∈ I, H' * i ∈ I) → (∀ i ∈ I, ∀ z ∈ Z, i * z ∈ I) → (∀ i ∈ I, Λ i = 0) → IsIntMod Z I H → IsIntMod Z I H' → FiniteDimensional ℂ ((Subalgebra.toSubmodule Z).map κ) → (∀ z ∈ Z, κ z = 0 → ∀ T, Λ (T * z) = 0) → FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun p : ℕ × ℕ => Λ (H ^ p.1 * H' ^ p.2))) := by
  first | exact @GlobalTheory.TorFin.finiteDimensional_span_pow_mul_pow | exact GlobalTheory.TorFin.finiteDimensional_span_pow_mul_pow | (intros; apply GlobalTheory.TorFin.finiteDimensional_span_pow_mul_pow <;> assumption)
