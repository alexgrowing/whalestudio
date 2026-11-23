import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsConeTangentAverage
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StAreaMultiplicity
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory

noncomputable section

def TangentJacComp.Statement : Prop :=
  ∀ (d n : ℕ) (L : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)) (π : Fin d → Fin n → ℂ),
    tangentJac π (LinearMap.range L) * areaJacobian (L.restrictScalars ℝ) =
      |LinearMap.det (((linProjₗ π).comp L).restrictScalars ℝ)|

end

end GroundTheory.Heights₂.Heights
