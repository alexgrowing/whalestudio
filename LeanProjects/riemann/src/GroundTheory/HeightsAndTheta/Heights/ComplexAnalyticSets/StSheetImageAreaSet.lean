import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSheetComass
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Matrix

open scoped ENNReal

noncomputable section

def SheetImageAreaSet.Statement : Prop :=
  ∀ (n d : ℕ) (A : Matrix (Fin d) (Fin n) ℂ) (U : Set (Fin d → ℂ)) (s : (Fin d → ℂ) → Fin n → ℂ),
    IsOpen U → DifferentiableOn ℂ s U → (∀ y ∈ U, A *ᵥ s y = y) →
    ∀ B : Set (EuclideanSpace ℂ (Fin d)), MeasurableSet B → (∀ y ∈ B, WithLp.ofLp y ∈ U) →
      μH[((2 * d : ℕ) : ℝ)] ((fun y => WithLp.toLp 2 (s (WithLp.ofLp y))) '' B) =
        ∫⁻ y in B, ENNReal.ofReal (sheetJac s (WithLp.ofLp y)) ∂(μH[((2 * d : ℕ) : ℝ)])

end

end GroundTheory.Heights₂.Heights
