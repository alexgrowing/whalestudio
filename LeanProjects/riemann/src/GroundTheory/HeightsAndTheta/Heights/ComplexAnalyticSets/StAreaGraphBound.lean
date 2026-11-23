import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsArea
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StGraphJacContinuous
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory

open scoped ENNReal NNReal

noncomputable section

def AreaGraphBound.Statement : Prop :=
  ∀ (k m : ℕ) (U : Set (EuclideanSpace ℝ (Fin k)))
    (F : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin m)),
    IsOpen U → ContDiffOn ℝ 1 F U → ∀ A ⊆ U, MeasurableSet A →
      ∀ δ : ℝ≥0, 0 < δ → δ < 1 →
        μH[(k : ℝ)] (realGraphPt F '' A) ≤
            ((1 + δ : ℝ≥0) : ℝ≥0∞) ^ (k + 1) *
              ∫⁻ x in A, ENNReal.ofReal (graphJac (fderiv ℝ F x :
                EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))) ∂(μH[(k : ℝ)]) ∧
          ((1 - δ : ℝ≥0) : ℝ≥0∞) ^ k *
              ∫⁻ x in A, ENNReal.ofReal (graphJac (fderiv ℝ F x :
                EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))) ∂(μH[(k : ℝ)]) ≤
            ((1 + δ : ℝ≥0) : ℝ≥0∞) * μH[(k : ℝ)] (realGraphPt F '' A)

end

end GroundTheory.Heights₂.Heights
