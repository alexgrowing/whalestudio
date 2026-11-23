import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CutoffHoloSmoothDbarFormula
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cutoff_holo_smooth_dbar_formula : ∀ (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M], ∀ (X : EtaleStein n M) (ψ : M → ℝ) (G : M → ℂ) (Ω : Set M) (δ b : ℝ) (θ : ℝ → ℝ), SmoothR n X.z ψ → ContDiff ℝ ∞ θ → (∀ t, b ≤ t → θ t = 0) → IsOpen Ω → (∀ e : OpenPartialHomeomorph M (V n), IsChart n X.z e → DifferentiableOn ℂ (G ∘ e.symm) (e.target ∩ e.symm ⁻¹' Ω)) → (∀ x, δ * ψ x ≤ b → x ∈ Ω) → Smooth n X.z (fun x => (θ (δ * ψ x) : ℂ) * G x) ∧ ∀ (x : M) (ξ : Fin n → ℂ), dbarDot n X.z (fun y => (θ (δ * ψ y) : ℂ) * G y) x ξ = ((deriv θ (δ * ψ x) * δ : ℝ) : ℂ) * G x * dbarDot n X.z (fun y => (ψ y : ℂ)) x ξ := by
  first | exact @GlobalTheory.L2Cutoff.cutoff_smooth_dbar | exact GlobalTheory.L2Cutoff.cutoff_smooth_dbar | (intros; apply GlobalTheory.L2Cutoff.cutoff_smooth_dbar <;> assumption)
