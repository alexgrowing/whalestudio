import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HoloLimitIncreasingWeights
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_holo_l2_bound_of_increasing_weights : ∀ (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M], ∀ (X : EtaleStein n M) (F0 : M → ℂ) (om : M → ℝ) (c : ℝ) (p : ℕ → M → ℝ) (q : M → ℝ) (F : ℕ → M → ℂ) (B : ℝ≥0∞), Continuous F0 → Continuous om → 0 < c → (∀ x, c ≤ om x ∧ om x ≤ 1) → (∀ k, SmoothR n X.z (p k)) → (∀ x, Antitone (fun k => p k x)) → (∀ x, Tendsto (fun k => p k x) atTop (𝓝 (q x))) → (∀ k, Holo n X.z (F k)) → B < ⊤ → (∀ k, ∫⁻ x, ENNReal.ofReal (‖F0 x - F k x‖ ^ 2 * (om x * Real.exp (-p k x))) ∂vol n X.z ≤ B) → ∃ G : M → ℂ, Holo n X.z G ∧ ∫⁻ x, ENNReal.ofReal (‖F0 x - G x‖ ^ 2 * (om x * Real.exp (-q x))) ∂vol n X.z ≤ B := by
  first | exact @GlobalTheory.holo_limit_increasing_weights | exact GlobalTheory.holo_limit_increasing_weights | (intros; apply GlobalTheory.holo_limit_increasing_weights <;> assumption)
