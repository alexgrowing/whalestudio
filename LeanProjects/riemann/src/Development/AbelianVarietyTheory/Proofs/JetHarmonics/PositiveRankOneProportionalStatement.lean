import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PositiveRankOneProportional
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.positive_rank_one_proportional : ∀ (T W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W] (l₀ La : T → W), (∀ v w, ContinuousLinearMap.adjoint ((innerSL ℂ (La v)).smulRight (l₀ w)) = (innerSL ℂ (La w)).smulRight (l₀ v)) → (∀ v ξ, (⟪ξ, ((innerSL ℂ (La v)).smulRight (l₀ v)) ξ⟫_ℂ).im = 0 ∧ 0 ≤ (⟪ξ, ((innerSL ℂ (La v)).smulRight (l₀ v)) ξ⟫_ℂ).re) → (∃ v, l₀ v ≠ 0) → ∃ c : ℝ, 0 ≤ c ∧ ∀ v, La v = (c : ℂ) • l₀ v := by
  first | exact @GlobalTheory.hermitian_rankOne_kernel_shape | exact GlobalTheory.hermitian_rankOne_kernel_shape | (intros; apply GlobalTheory.hermitian_rankOne_kernel_shape <;> assumption)
