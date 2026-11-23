import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLimitFamilyOfFiniteCoefficients
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_limit_family_of_finite_coefficients' : ∀ (σ I R : Type) [Finite σ] [Finite I] [Finite R] (F : ℕ → I → (σ →₀ ℕ) → R), ∃ G : I → (σ →₀ ℕ) → R, ∀ N M₀ : ℕ, ∃ M, M₀ ≤ M ∧ ∀ x m, m.degree ≤ N → F M x m = G x m := by
  first | exact @GlobalTheory.exists_limit_family_of_finite_coefficients | exact GlobalTheory.exists_limit_family_of_finite_coefficients | (intros; apply GlobalTheory.exists_limit_family_of_finite_coefficients <;> assumption)
