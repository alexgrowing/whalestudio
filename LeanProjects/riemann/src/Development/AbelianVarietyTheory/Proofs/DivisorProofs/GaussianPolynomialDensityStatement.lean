import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussianPolynomialDensity
import Mathlib
open SchwartzMap
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaussian_polynomial_density : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (Q : V →ₗ[ℝ] V →ₗ[ℝ] ℂ) (c : ℝ), 0 < c → (∀ x, c * ‖x‖ ^ 2 ≤ (Q x x).re) →
    ∀ g : SchwartzMap V ℂ, (∀ x, g x = Complex.exp (-(Q x x))) →
    ∀ N : Submodule ℂ (SchwartzMap V ℂ),
    (∀ (j : ℕ) (M : ContinuousMultilinearMap ℝ (fun _ : Fin j => V) ℂ),
      ∃ f ∈ N, ∀ x, f x = M (fun _ => x) * g x) →
    ∀ (ψ : SchwartzMap V ℂ) (A ρ : ℝ), (∀ (j : ℕ) (y : V), ‖iteratedFDeriv ℝ j ψ y‖ ≤ A * ρ ^ j) →
    ∀ F : SchwartzMap V ℂ, (∀ x, F x = ψ x * g x) → F ∈ N.topologicalClosure := by
  first | exact @GlobalTheory.gaussian_mul_mem_closure_of_taylor | exact GlobalTheory.gaussian_mul_mem_closure_of_taylor | (intros; apply GlobalTheory.gaussian_mul_mem_closure_of_taylor <;> assumption)
