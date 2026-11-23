import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzLogDerivativeGaussian
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_log_derivative_gaussian : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (f : SchwartzMap V ℂ), f ≠ 0 →
    ∀ (P : V → V →ₗ[ℝ] ℂ), (∀ x α, fderiv ℝ (⇑f) x α = P α x * f x) →
    ∃ (Q : V →ₗ[ℝ] V →ₗ[ℝ] ℂ) (z : ℂ), (∀ x, x ≠ 0 → 0 < (Q x x).re) ∧ ∀ x, f x = z * Complex.exp (-(Q x x)) := by
  first | exact @GlobalTheory.schwartz_gaussian_of_fderiv_eq_linear_mul | exact GlobalTheory.schwartz_gaussian_of_fderiv_eq_linear_mul | (intros; apply GlobalTheory.schwartz_gaussian_of_fderiv_eq_linear_mul <;> assumption)
