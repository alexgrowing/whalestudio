import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsArea
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.RingKrullDimQuotBotOne
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.FrameProjEq
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MeasureTheory Measure Metric Module

open scoped ENNReal

noncomputable section

namespace AreaLinear

theorem areaFactor_eq_normDet {k m : ℕ}
    (L : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) :
    areaFactor L = L.normDet := by
  unfold areaFactor
  rw [← LinearMap.normDet_sq L]
  push_cast
  exact Real.sqrt_sq (LinearMap.normDet_nonneg L)

theorem dividedDifference_real_holds : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.AreaLinear.Statement := by
  intro k m L _ A
  have h := LinearMap.hausdorffMeasure_image L A
  rw [finrank_euclideanSpace_fin] at h
  rw [h, areaFactor_eq_normDet]

def LebesgueForm : Prop :=
  ∀ (k m : ℕ) (L : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)),
    Function.Injective L → ∀ A : Set (EuclideanSpace ℝ (Fin k)),
      μH[(k : ℝ)] (L '' A) = ENNReal.ofReal (areaFactor L) * volume A

theorem statement_iff :
    GroundTheory.Heights₂.Heights.AreaLinear.Statement ↔
      GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.AreaLinear.Statement :=
  Iff.rfl

end AreaLinear

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
