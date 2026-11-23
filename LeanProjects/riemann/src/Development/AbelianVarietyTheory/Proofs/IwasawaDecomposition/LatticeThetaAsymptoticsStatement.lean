import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeThetaAsymptotics
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyRayDataOfNeZero
open Complex Filter Asymptotics
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_theta_asymptotics : ∀ (w₁ w₂ x₀ : ℂ), (starRingEnd ℂ w₁ * w₂).im ≠ 0 → (∀ m n : ℤ, x₀ + m * w₁ + n * w₂ ≠ 0) → ∃ c : ℝ, 0 < c ∧ (fun t : ℝ => ∑' p : ℤ × ℤ, Real.exp (-Real.pi * t * ‖x₀ + p.1 * w₁ + p.2 * w₂‖ ^ 2)) =O[atTop] (fun t => Real.exp (-c * t)) ∧ (fun t : ℝ => (∑' p : ℤ × ℤ, Real.exp (-Real.pi * t * ‖x₀ + p.1 * w₁ + p.2 * w₂‖ ^ 2)) - 1 / (t * |(starRingEnd ℂ w₁ * w₂).im|)) =O[nhdsWithin 0 (Set.Ioi 0)] (fun t => Real.exp (-c / t)) := by
  first | exact @GlobalTheory.PlaneTheta.theta_asymptotics | exact GlobalTheory.PlaneTheta.theta_asymptotics | (intros; apply GlobalTheory.PlaneTheta.theta_asymptotics <;> assumption)
