import Mathlib

open MeasureTheory Measure
open scoped ENNReal

set_option linter.dupNamespace false

namespace Formalism.L2.SG.Pf.QuotIndep

def QuotIndep : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (S : Subgroup G), IsClosed (S : Set G) →
    ∀ (μS : Measure S) [μS.IsMulLeftInvariant] [μS.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μS]
      [IsOpenPosMeasure μS] [SFinite μS] (μ ν₁ ν₂ : Measure G),
      (∀ f : G → ℝ≥0∞, Measurable f → ∫⁻ x, f x ∂μ = ∫⁻ x, ∫⁻ s, f ((s : G) * x) ∂μS ∂ν₁) →
      (∀ f : G → ℝ≥0∞, Measurable f → ∫⁻ x, f x ∂μ = ∫⁻ x, ∫⁻ s, f ((s : G) * x) ∂μS ∂ν₂) →
      ∀ f : G → ℝ≥0∞, Measurable f → (∀ (s : S) (x : G), f ((s : G) * x) = f x) →
        ∫⁻ x, f x ∂ν₁ = ∫⁻ x, f x ∂ν₂

end Formalism.L2.SG.Pf.QuotIndep
