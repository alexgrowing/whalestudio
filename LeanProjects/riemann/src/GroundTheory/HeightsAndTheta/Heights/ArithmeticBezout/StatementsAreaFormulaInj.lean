import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StAreaMultiplicity
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Module

open scoped ENNReal

def AreaFormulaInj.Statement : Prop :=
  ∀ (E F : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] (k : ℕ),
    finrank ℝ E = k →
    ∀ (U A : Set E) (f : E → F) (g : F → ℝ≥0∞),
      IsOpen U → ContDiffOn ℝ 1 f U → A ⊆ U → MeasurableSet A → Set.InjOn f A → Measurable g →
        ∫⁻ y in f '' A, g y ∂(μH[(k : ℝ)]) =
          ∫⁻ x in A, g (f x) * ENNReal.ofReal (areaJacobian (fderiv ℝ f x : E →ₗ[ℝ] F))
            ∂(μH[(k : ℝ)])

end GroundTheory.Heights₂.Heights
