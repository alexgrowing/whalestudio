import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MetricSmoothBiholomorphicTransfer
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HolSprayApply
open Filter Topology Matrix
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.metric_smooth_biholomorphic_transfer : ∀ (d : ℕ) (U U' : Set (ReciprocityTheory.L2DbarEstimates.V d)) (τ : ReciprocityTheory.L2DbarEstimates.V d → ReciprocityTheory.L2DbarEstimates.V d) (b b' : ReciprocityTheory.L2DbarEstimates.V d → Matrix (Fin d) (Fin d) ℂ), IsOpen U → DifferentiableOn ℂ τ U → Set.MapsTo τ U U' → (∀ k l, ContDiffOn ℝ ∞ (fun v => b' v k l) U') → (∀ v ∈ U, ∀ ξ ζ : ReciprocityTheory.L2DbarEstimates.V d, (ξ.ofLp ᵥ* b v) ⬝ᵥ star ζ.ofLp = ((fderiv ℂ τ v ξ).ofLp ᵥ* b' (τ v)) ⬝ᵥ star (fderiv ℂ τ v ζ).ofLp) → ∀ k l, ContDiffOn ℝ ∞ (fun v => b v k l) U := by
  first | exact @GlobalTheory.metric_pullback_contDiffOn | exact GlobalTheory.metric_pullback_contDiffOn | (intros; apply GlobalTheory.metric_pullback_contDiffOn <;> assumption)
