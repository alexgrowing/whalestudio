import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExtensionAcrossZeroOfExpTwoPiIBound
import Mathlib
open Metric Filter Topology Set
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.extension_across_zero_of_exp_two_pi_I_bound : ∀ (H : ℂ → ℂ) (r C : ℝ) (N : ℕ), 0 < r → DifferentiableOn ℂ H (Metric.ball (0 : ℂ) r \ {0}) → (∀ t ∈ Metric.ball (0 : ℂ) r, t ≠ 0 → ‖Complex.exp (2 * Real.pi * Complex.I * H t)‖ * ‖t‖ ^ N ≤ C) → ∃ G : ℂ → ℂ, DifferentiableOn ℂ G (Metric.ball (0 : ℂ) r) ∧ ∀ t ∈ Metric.ball (0 : ℂ) r, t ≠ 0 → G t = H t := by
  first | exact @GlobalTheory.holomorphic_extension_of_exp_two_pi_I_bound | exact GlobalTheory.holomorphic_extension_of_exp_two_pi_I_bound | (intros; apply GlobalTheory.holomorphic_extension_of_exp_two_pi_I_bound <;> assumption)
