import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussianQuadraticFormSchwartzBounds
import Mathlib
open SchwartzMap Filter Topology
open scoped Nat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaussian_quadratic_form_schwartz_bounds : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (Q : V →ₗ[ℝ] V →ₗ[ℝ] ℂ) (c : ℝ), 0 < c → (∀ x, c * ‖x‖ ^ 2 ≤ (Q x x).re) →
    ∀ (b k : ℕ) (B : ℝ), ∃ C : ℝ, ∀ x : V,
      ‖x‖ ^ k * Real.exp (B * ‖x‖) * ‖iteratedFDeriv ℝ b (fun y => Complex.exp (-(Q y y))) x‖ ≤ C := by
  first | exact @GlobalTheory.gauss_weighted_iteratedFDeriv_bounded | exact GlobalTheory.gauss_weighted_iteratedFDeriv_bounded | (intros; apply GlobalTheory.gauss_weighted_iteratedFDeriv_bounded <;> assumption)
