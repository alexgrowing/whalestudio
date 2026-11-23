import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory

noncomputable section

def WeightedAreaFormula.Statement : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] (A : Set E) (f : E → E) (H : E → ℝ),
    IsOpen A → DifferentiableOn ℝ f A → (∀ y, {x | x ∈ A ∧ f x = y}.Finite) →
    IntegrableOn (fun x => |(fderiv ℝ f x).det| * H x) A μ →
      Integrable (fun y => ∑ᶠ x ∈ {x | x ∈ A ∧ f x = y}, H x) μ ∧
        ∫ y, (∑ᶠ x ∈ {x | x ∈ A ∧ f x = y}, H x) ∂μ = ∫ x in A, |(fderiv ℝ f x).det| * H x ∂μ

end

end GroundTheory.Heights₂.Heights
