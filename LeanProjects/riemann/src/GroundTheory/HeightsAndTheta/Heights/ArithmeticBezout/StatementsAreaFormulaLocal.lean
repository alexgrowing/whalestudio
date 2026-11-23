import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StAreaMultiplicity
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Module

open scoped ENNReal

def AreaFormulaLocal.Statement : Prop :=
  ∀ (E F : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] (k : ℕ),
    finrank ℝ E = k →
    ∀ (U : Set E) (f : E → F) (x₀ : E),
      IsOpen U → ContDiffOn ℝ 1 f U → x₀ ∈ U → Function.Injective (fderiv ℝ f x₀) →
        ∃ V : Set E, IsOpen V ∧ x₀ ∈ V ∧ V ⊆ U ∧ ∀ B ⊆ V, MeasurableSet B →
          μH[(k : ℝ)] (f '' B) =
            ∫⁻ x in B, ENNReal.ofReal (areaJacobian (fderiv ℝ f x : E →ₗ[ℝ] F)) ∂(μH[(k : ℝ)])

end GroundTheory.Heights₂.Heights
