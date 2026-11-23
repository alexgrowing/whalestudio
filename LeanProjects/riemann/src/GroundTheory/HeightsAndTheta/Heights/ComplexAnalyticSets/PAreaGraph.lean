import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsArea
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StAreaGraphBound
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Filter Topology

open scoped ENNReal NNReal

theorem AreaGraph.proof (h : AreaGraphBound.Statement) : AreaGraph.Statement := by
  intro k m U F hU hF A hAU hA

  change μH[(k : ℝ)] (realGraphPt F '' A) =
    ∫⁻ x in A, ENNReal.ofReal (graphJac (fderiv ℝ F x :
      EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))) ∂(μH[(k : ℝ)])
  set S := μH[(k : ℝ)] (realGraphPt F '' A)
  set I := ∫⁻ x in A, ENNReal.ofReal (graphJac (fderiv ℝ F x :
      EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))) ∂(μH[(k : ℝ)])

  have hplus : ∀ j : ℕ,
      Tendsto (fun δ : ℝ≥0 => ((1 + δ : ℝ≥0) : ℝ≥0∞) ^ j) (𝓝[>] 0) (𝓝 1) := by
    intro j
    have hcont : Continuous (fun δ : ℝ≥0 => ((1 + δ : ℝ≥0) : ℝ≥0∞) ^ j) :=
      (ENNReal.continuous_pow j).comp (ENNReal.continuous_coe.comp (continuous_const.add continuous_id))
    simpa using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  have hminus : ∀ j : ℕ,
      Tendsto (fun δ : ℝ≥0 => ((1 - δ : ℝ≥0) : ℝ≥0∞) ^ j) (𝓝[>] 0) (𝓝 1) := by
    intro j
    have hcont : Continuous (fun δ : ℝ≥0 => ((1 - δ : ℝ≥0) : ℝ≥0∞) ^ j) :=
      (ENNReal.continuous_pow j).comp (ENNReal.continuous_coe.comp (continuous_const.sub continuous_id))
    simpa using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds

  have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ≥0), 0 < δ ∧ δ < 1 := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ≥0) < 1 from one_pos)] with δ hδ
    exact hδ
  have hb : ∀ᶠ δ in 𝓝[>] (0 : ℝ≥0),
      S ≤ ((1 + δ : ℝ≥0) : ℝ≥0∞) ^ (k + 1) * I ∧
        ((1 - δ : ℝ≥0) : ℝ≥0∞) ^ k * I ≤ ((1 + δ : ℝ≥0) : ℝ≥0∞) * S := by
    filter_upwards [hev] with δ hδ
    exact h k m U F hU hF A hAU hA δ hδ.1 hδ.2
  apply le_antisymm
  · have hlim := ENNReal.Tendsto.mul_const (hplus (k + 1)) (b := I) (Or.inl one_ne_zero)
    rw [one_mul] at hlim
    exact le_of_tendsto_of_tendsto tendsto_const_nhds hlim (hb.mono fun δ hδ => hδ.1)
  · have hlim₁ := ENNReal.Tendsto.mul_const (hminus k) (b := I) (Or.inl one_ne_zero)
    have hlim₂ := ENNReal.Tendsto.mul_const (by simpa using hplus 1) (b := S) (Or.inl one_ne_zero)
    rw [one_mul] at hlim₁ hlim₂
    exact le_of_tendsto_of_tendsto hlim₁ hlim₂ (hb.mono fun δ hδ => hδ.2)

end GroundTheory.Heights₂.Heights
