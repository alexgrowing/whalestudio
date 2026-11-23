import Mathlib

universe u

namespace HeckeCharacterZeroLocus

open MeasureTheory Pointwise

def BruhatFunctionExistsVariant : Prop :=
  ∀ (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [T2Space G] [MeasurableSpace G] [BorelSpace G] (H : Subgroup G), IsClosed (H : Set G) →
    ∀ (μ : Measure H), μ.IsHaarMeasure →
      ∃ β : G → ℝ, Continuous β ∧ (∀ x, 0 ≤ β x) ∧
        (∀ K : Set G, IsCompact K → IsCompact (tsupport β ∩ (K * (H : Set G)))) ∧
        ∀ x : G, ∫ h : H, β (x * (h : G)) ∂μ = 1

end HeckeCharacterZeroLocus
