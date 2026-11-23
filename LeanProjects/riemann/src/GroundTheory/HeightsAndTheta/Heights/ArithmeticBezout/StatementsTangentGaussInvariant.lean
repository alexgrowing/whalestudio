import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsConeTangentAverage
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Module

open scoped ENNReal

noncomputable section

def TangentGaussInvariant.Statement : Prop :=
  ∀ (n m : ℕ), 0 < m → m ≤ n → ∀ T : Submodule ℂ (EuclideanSpace ℂ (Fin n)), finrank ℂ T = m →
    ∀ y ∈ T,
      ∫⁻ π : Fin m → Fin n → ℂ, matGauss π *
          (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1).indicator 1 (linProj π y) *
            ENNReal.ofReal (tangentJac π T) =
        tangentGaussProfile n m ‖y‖

end

end GroundTheory.Heights₂.Heights
