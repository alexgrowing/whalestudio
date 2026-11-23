import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlowDerivativeIntegralByParts
import Mathlib
open MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flow_derivative_integral_by_parts : ∀ {H : Type} [inst : Group H] [inst_1 : TopologicalSpace H] [inst_2 : IsTopologicalGroup H] [inst_3 : LocallyCompactSpace H] [inst_4 : SecondCountableTopology H] [inst_5 : T2Space H] [inst_6 : MeasurableSpace H] [inst_7 : BorelSpace H] (μ : Measure H) [inst_8 : μ.IsHaarMeasure] (𝓕 : Set H) (γ : Multiplicative ℝ →* H), Continuous γ → ∀ (f f₁ : H → ℂ), (∀ x, HasDerivAt (fun t : ℝ => f (x * γ (Multiplicative.ofAdd t))) (f₁ x) 0) → Continuous f₁ → ∀ (t : ℝ), t ≠ 0 → eLpNorm (fun x => (t : ℂ)⁻¹ * (f (x * γ (Multiplicative.ofAdd t)) - f x) - f₁ x) 2 (μ.restrict 𝓕) ≤ ⨆ s ∈ Set.uIcc 0 t, eLpNorm (fun x => f₁ (x * γ (Multiplicative.ofAdd s)) - f₁ x) 2 (μ.restrict 𝓕) := by
  first | exact @GlobalTheory.eLpNorm_diffQuot_sub_deriv_le_iSup | exact GlobalTheory.eLpNorm_diffQuot_sub_deriv_le_iSup | (intros; apply GlobalTheory.eLpNorm_diffQuot_sub_deriv_le_iSup <;> assumption)
