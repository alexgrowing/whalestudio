import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory

open scoped ENNReal

noncomputable section

def AreaMultiplicityWeight.Statement : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] (A : Set E) (f : E → E)
    (f' : E → E →L[ℝ] E), MeasurableSet A → (∀ x ∈ A, HasFDerivWithinAt f (f' x) A x) →
      AEMeasurable (fun y => (({x ∈ A | f x = y}.encard : ℕ∞) : ℝ≥0∞)) μ ∧
        ∀ g : E → ℝ≥0∞, Measurable g →
          ∫⁻ x in A, g (f x) * ENNReal.ofReal |(f' x).det| ∂μ =
            ∫⁻ y, (({x ∈ A | f x = y}.encard : ℕ∞) : ℝ≥0∞) * g y ∂μ

end

end GroundTheory.Heights₂.Heights
