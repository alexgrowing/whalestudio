import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeEpsteinZetaContinuation
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyRayDataOfNeZero
open Complex Filter Asymptotics
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_epstein_zeta_continuation : ∀ (w₁ w₂ x₀ : ℂ), (starRingEnd ℂ w₁ * w₂).im ≠ 0 → (∀ m n : ℤ, x₀ + m * w₁ + n * w₂ ≠ 0) → ∃ Z : ℂ → ℂ, Differentiable ℂ Z ∧ Z 1 = (Real.pi / |(starRingEnd ℂ w₁ * w₂).im| : ℝ) ∧ Z (-1) = 0 ∧ ∀ s : ℂ, 1 < s.re → Summable (fun p : ℤ × ℤ => ((‖x₀ + p.1 * w₁ + p.2 * w₂‖ ^ 2 : ℝ) : ℂ) ^ (-s)) ∧ Z s = (s - 1) * ∑' p : ℤ × ℤ, ((‖x₀ + p.1 * w₁ + p.2 * w₂‖ ^ 2 : ℝ) : ℂ) ^ (-s) := by
  first | exact @GlobalTheory.epsteinZeta_shifted_continuation | exact GlobalTheory.epsteinZeta_shifted_continuation | (intros; apply GlobalTheory.epsteinZeta_shifted_continuation <;> assumption)
