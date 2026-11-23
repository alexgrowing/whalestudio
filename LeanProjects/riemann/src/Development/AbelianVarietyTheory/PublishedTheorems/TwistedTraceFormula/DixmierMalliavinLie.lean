import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset

noncomputable section

open MeasureTheory
open scoped Topology ContDiff Manifold

namespace GlobalTheory.Published

def DixmierMalliavinLie : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (G : Type) [Group G] [TopologicalSpace G] [T2Space G] [SecondCountableTopology G] [ChartedSpace E G]
    [LieGroup 𝓘(ℝ, E) ∞ G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure],
    ∀ V ∈ 𝓝 (1 : G), ∀ f : G → ℂ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ f → HasCompactSupport f →
      ∃ (N : ℕ) (g h : Fin N → G → ℂ),
        (∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ (g i) ∧ HasCompactSupport (g i) ∧
          ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ (h i) ∧ HasCompactSupport (h i) ∧
          tsupport (g i) ⊆ V ∧ tsupport (h i) ⊆ tsupport f) ∧
        ∀ y, f y = ∑ i, ∫ x, g i x * h i (x⁻¹ * y) ∂μ

example : LieGroup 𝓘(ℝ, ℝ) ∞ ℝˣ := inferInstance

end GlobalTheory.Published

end
