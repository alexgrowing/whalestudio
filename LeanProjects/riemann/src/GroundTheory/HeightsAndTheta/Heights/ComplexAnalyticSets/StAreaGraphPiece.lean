import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsArea
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StGraphJacContinuous
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory

open scoped ENNReal NNReal

noncomputable section

def AreaGraphPiece.Statement : Prop :=
  ∀ (k m : ℕ) (F : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin m))
    (A : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin m)) (δ : ℝ≥0)
    (t : Set (EuclideanSpace ℝ (Fin k))), δ < 1 → ApproximatesLinearOn F A t δ →
      μH[(k : ℝ)] (realGraphPt F '' t) ≤
          ((1 + δ : ℝ≥0) : ℝ≥0∞) ^ k *
            ENNReal.ofReal (graphJac (A : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))) *
              μH[(k : ℝ)] t ∧
        ((1 - δ : ℝ≥0) : ℝ≥0∞) ^ k *
            ENNReal.ofReal (graphJac (A : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))) *
              μH[(k : ℝ)] t ≤
          μH[(k : ℝ)] (realGraphPt F '' t)

end

end GroundTheory.Heights₂.Heights
