import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExponentialChartSmoothForm
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousAndSmul
open Filter Topology Set Metric MeasureTheory GlobalTheory.ChernReg
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exponential_chart_smooth_form : ∀ (d : ℕ) (U : Set (Fin d → ℂ)) (N : Set ((Fin d → ℂ) × (Fin d → ℂ))) (G : (Fin d → ℂ) × (Fin d → ℂ) → Fin d → ℂ) (q : (Fin d → ℂ) → (Fin d → ℂ) → ℝ) (z₀ : Fin d → ℂ), IsOpen U → z₀ ∈ U → IsOpen N → (z₀, 0) ∈ N → ContDiffOn ℝ ∞ G N → G (z₀, 0) = z₀ → HasFDerivAt (fun ξ => G (z₀, ξ)) (ContinuousLinearMap.id ℝ (Fin d → ℂ)) 0 → ContDiffOn ℝ ∞ (fun p : (Fin d → ℂ) × (Fin d → ℂ) => q p.1 p.2) (U ×ˢ Set.univ) → (∀ z ∈ U, ∀ (t : ℝ) ξ, q z (t • ξ) = t ^ 2 * q z ξ) → (∀ z ∈ U, ∀ ξ, ξ ≠ 0 → 0 < q z ξ) → ∃ δ : ℝ, 0 < δ ∧ ∃ U' : Set (Fin d → ℂ), IsOpen U' ∧ z₀ ∈ U' ∧ U' ⊆ U ∧ (∀ z ∈ U', ∀ t : ℝ, 0 < t → t < δ → ∀ ξ, q z ξ < 1 → (z, t • ξ) ∈ N) ∧ ∀ ψ : (Fin d → ℂ) → ℝ, MeasureTheory.LocallyIntegrableOn ψ U MeasureTheory.volume → ∀ t : ℝ, 0 < t → t < δ → ContDiffOn ℝ ∞ (fun z => GlobalTheory.ChernReg.mean (q z) fun ξ => ψ (G (z, t • ξ))) U' := by
  first | exact @GlobalTheory.contDiffOn_mean_along_family | exact GlobalTheory.contDiffOn_mean_along_family | (intros; apply GlobalTheory.contDiffOn_mean_along_family <;> assumption)
