import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FundamentalDomainFlowIntegralIdentity
import Mathlib
open MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fundamental_domain_flow_integral_identity : ∀ {H : Type} [inst : Group H] [inst_1 : TopologicalSpace H] [inst_2 : IsTopologicalGroup H] [inst_3 : LocallyCompactSpace H] [inst_4 : SecondCountableTopology H] [inst_5 : T2Space H] [inst_6 : MeasurableSpace H] [inst_7 : BorelSpace H] (μ : Measure H) [inst_8 : μ.IsHaarMeasure] (Γ : Subgroup H) [inst_9 : Countable Γ] (𝓕 : Set H), IsFundamentalDomain Γ 𝓕 μ → ∀ (γ : Multiplicative ℝ →* H), Continuous γ → ∀ (f₁ : H → ℂ), Continuous f₁ → (∀ g ∈ Γ, ∀ x, f₁ (g * x) = f₁ x) → IntegrableOn (fun x => ‖f₁ x‖ ^ 2) 𝓕 μ → Tendsto (fun s : ℝ => eLpNorm (fun x => f₁ (x * γ (Multiplicative.ofAdd s)) - f₁ x) 2 (μ.restrict 𝓕)) (𝓝 0) (𝓝 0) := by
  first | exact @GlobalTheory.RightTranslationL2Continuity.tendsto_eLpNorm_mul_right_sub | exact GlobalTheory.RightTranslationL2Continuity.tendsto_eLpNorm_mul_right_sub | (intros; apply GlobalTheory.RightTranslationL2Continuity.tendsto_eLpNorm_mul_right_sub <;> assumption)
