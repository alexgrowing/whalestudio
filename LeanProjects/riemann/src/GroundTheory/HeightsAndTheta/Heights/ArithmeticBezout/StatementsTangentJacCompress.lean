import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsConeTangentAverage
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Module

noncomputable section

def TangentJacCompress.Statement : Prop :=
  ∀ (n m : ℕ) (π : Fin m → Fin n → ℂ) (T : Submodule ℂ (EuclideanSpace ℂ (Fin n))),
    ((tangentJac π T : ℝ) : ℂ) =
      (T.starProjection ∘L (LinearMap.toContinuousLinearMap (linProjₗ π)).adjoint ∘L
          LinearMap.toContinuousLinearMap (linProjₗ π) ∘L T.starProjection +
        (1 - T.starProjection)).det

end

end GroundTheory.Heights₂.Heights
