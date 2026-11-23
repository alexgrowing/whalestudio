import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MetricJetTransferBiholomorphic
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HolSprayApply
open Filter Topology Matrix
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.metric_jet_transfer_biholomorphic : ∀ (d : ℕ) (U U' : Set (ReciprocityTheory.L2DbarEstimates.V d)) (τ : ReciprocityTheory.L2DbarEstimates.V d → ReciprocityTheory.L2DbarEstimates.V d) (b b' : ReciprocityTheory.L2DbarEstimates.V d → Matrix (Fin d) (Fin d) ℂ), IsOpen U → IsOpen U' → DifferentiableOn ℂ τ U → Set.MapsTo τ U U' → (∀ k l, ContDiffOn ℝ ∞ (fun v => b v k l) U) → (∀ k l, ContDiffOn ℝ ∞ (fun v => b' v k l) U') → (∀ v ∈ U, IsUnit (b v).det) → (∀ v ∈ U', IsUnit (b' v).det) → (∀ v ∈ U, ∀ ξ ζ : ReciprocityTheory.L2DbarEstimates.V d, (ξ.ofLp ᵥ* b v) ⬝ᵥ star ζ.ofLp = ((fderiv ℂ τ v ξ).ofLp ᵥ* b' (τ v)) ⬝ᵥ star (fderiv ℂ τ v ζ).ofLp) → ∀ z ∈ U, ∀ ξ : ReciprocityTheory.L2DbarEstimates.V d, fderiv ℂ τ z (GlobalTheory.ChernReg.christoffel b z ξ) = GlobalTheory.ChernReg.christoffel b' (τ z) (fderiv ℂ τ z ξ) + fderiv ℂ (fderiv ℂ τ) z ξ ξ := by
  first | exact @GlobalTheory.ChernReg.chris_transform | exact GlobalTheory.ChernReg.chris_transform | (intros; apply GlobalTheory.ChernReg.chris_transform <;> assumption)
