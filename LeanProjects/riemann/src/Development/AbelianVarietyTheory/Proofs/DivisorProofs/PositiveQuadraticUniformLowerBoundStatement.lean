import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PositiveQuadraticUniformLowerBound
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousAndSmul
open Filter Topology Set Metric MeasureTheory GlobalTheory.ChernReg
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.positive_quadratic_uniform_lower_bound : ∀ (d : ℕ) (U Kc : Set (Fin d → ℂ)) (q : (Fin d → ℂ) → (Fin d → ℂ) → ℝ), IsCompact Kc → Kc ⊆ U → ContinuousOn (fun p : (Fin d → ℂ) × (Fin d → ℂ) => q p.1 p.2) (U ×ˢ Set.univ) → (∀ z ∈ U, ∀ (t : ℝ) ξ, q z (t • ξ) = t ^ 2 * q z ξ) → (∀ z ∈ U, ∀ ξ, ξ ≠ 0 → 0 < q z ξ) → ∃ m : ℝ, 0 < m ∧ ∀ z ∈ Kc, ∀ ξ, m * ‖ξ‖ ^ 2 ≤ q z ξ := by
  first | exact @GlobalTheory.uniformLowerBound_quadraticLike | exact GlobalTheory.uniformLowerBound_quadraticLike | (intros; apply GlobalTheory.uniformLowerBound_quadraticLike <;> assumption)
