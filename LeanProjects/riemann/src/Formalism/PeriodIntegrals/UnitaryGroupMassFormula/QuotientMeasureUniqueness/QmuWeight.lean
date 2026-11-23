import Mathlib

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace PI.QuotMeasUniqW

def QmuWeight : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (H : Subgroup G), IsClosed (H : Set G) →
    ∀ ν : Measure H, ν.IsHaarMeasure →
      ∃ w : G → ℝ≥0∞, Measurable w ∧
        ∀ g : G, (∫⁻ h, w (g * (h : G)) ∂ν) ≠ 0 ∧ (∫⁻ h, w (g * (h : G)) ∂ν) ≠ ⊤

def QmuLift : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (H : Subgroup G), IsClosed (H : Set G) →
    ∀ ν : Measure H, ν.IsHaarMeasure →
    ∀ ρ : Measure (G ⧸ H), (∀ K : Set (G ⧸ H), IsCompact K → ρ K < ⊤) →
      (∀ (g : G) (s : Set (G ⧸ H)), MeasurableSet s → ρ ((fun y => g • y) ⁻¹' s) = ρ s) →
      ∃ l : Measure G, l.IsMulLeftInvariant ∧ IsFiniteMeasureOnCompacts l ∧
        ∀ f : G → ℝ≥0∞, Measurable f →
          ∫⁻ x, f x ∂l = ∫⁻ y, (∫⁻ h, f (y.out * (h : G)) ∂ν) ∂ρ

end PI.QuotMeasUniqW
