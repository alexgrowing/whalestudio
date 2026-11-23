import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegrableOnVerticalRayNormIntegralLe
open MeasureTheory Filter Topology Set
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrableOn_vertical_ray_norm_integral_le : ∀ (g : ℂ → ℂ) (K c : ℝ) (m : ℕ) (τ : ℂ), ContinuousOn g {z : ℂ | 0 < z.im} → 0 < c →
    (∀ z : ℂ, 1 ≤ z.im → ‖g z‖ ≤ K * Real.exp (-c * z.im) * (1 + ‖z‖) ^ m) → 1 ≤ τ.im →
    IntegrableOn (fun s : ℝ => g (τ + s * Complex.I)) (Ioi 0) ∧
      ‖∫ s in Ioi (0:ℝ), g (τ + s * Complex.I)‖ ≤
        K * Real.exp (-c * τ.im) * (1 + ‖τ‖) ^ m * ∫ s in Ioi (0:ℝ), Real.exp (-c * s) * (1 + s) ^ m := by
  first | exact @GlobalTheory.vertRay_integral_expPow_bound | exact GlobalTheory.vertRay_integral_expPow_bound | (intros; apply GlobalTheory.vertRay_integral_expPow_bound <;> assumption)
