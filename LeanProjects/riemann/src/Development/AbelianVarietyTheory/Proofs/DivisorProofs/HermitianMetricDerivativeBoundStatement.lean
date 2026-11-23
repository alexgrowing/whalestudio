import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianMetricDerivativeBound
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WirtConst
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DualGramInterpGram
open GlobalTheory.MatDeriv GlobalTheory.GradedNorm Matrix
open scoped ComplexOrder

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_metric_derivative_bound : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (m : ℕ) (S : Set E) (Hh H0 : E → Matrix (Fin m) (Fin m) ℂ) (rr : E → ℝ) (q : E → E → ℝ) (μ K c₀ C₀ : ℝ), IsOpen S → 0 < c₀ → 0 ≤ μ →
  (∀ w ∈ S, 1 ≤ rr w ∧ (Hh w).PosDef ∧ (H0 w).PosDef ∧ ∀ a b, DifferentiableAt ℝ (fun w' => Hh w' a b) w ∧ DifferentiableAt ℝ (fun w' => H0 w' a b) w) →
  (∀ w ∈ S, ∀ v : Fin m → ℂ, c₀ * ‖v‖ ^ 2 ≤ (star v ⬝ᵥ H0 w *ᵥ v).re ∧ (star v ⬝ᵥ H0 w *ᵥ v).re ≤ C₀ * ‖v‖ ^ 2 ∧
    rr w ^ (-μ) * (star v ⬝ᵥ H0 w *ᵥ v).re ≤ (star v ⬝ᵥ Hh w *ᵥ v).re ∧ (star v ⬝ᵥ Hh w *ᵥ v).re ≤ rr w ^ μ * (star v ⬝ᵥ H0 w *ᵥ v).re) →
  (∀ w ∈ S, ∀ ξ : E, c₀ * ‖ξ‖ ≤ q w ξ ∧ ∀ v : Fin m → ℂ, ‖((H0 w)⁻¹ * wirt H0 w ξ) *ᵥ v‖ ≤ C₀ * ‖ξ‖ * ‖v‖ ∧
    ‖((Hh w)⁻¹ * wirt Hh w ξ - (H0 w)⁻¹ * wirt H0 w ξ) *ᵥ v‖ ≤ K * rr w ^ μ * Real.exp (rr w / 2) * q w ξ * ‖v‖) →
  ∃ K' : ℝ, 0 ≤ K' ∧ ∀ w ∈ S, ∀ i : Fin m,
    DifferentiableAt ℝ (fun w' => Real.log (grSq (Hh w') i) - Real.log (grSq (H0 w') i)) w ∧
    ∀ ξ : E, |fderiv ℝ (fun w' => Real.log (grSq (Hh w') i) - Real.log (grSq (H0 w') i)) w ξ| ≤
      K' * rr w ^ (3 * μ) * Real.exp (rr w / 2) * q w ξ := by
  first | exact @GlobalTheory.GradedLogDeriv.deriv_log_grSq_ratio | exact GlobalTheory.GradedLogDeriv.deriv_log_grSq_ratio | (intros; apply GlobalTheory.GradedLogDeriv.deriv_log_grSq_ratio <;> assumption)
