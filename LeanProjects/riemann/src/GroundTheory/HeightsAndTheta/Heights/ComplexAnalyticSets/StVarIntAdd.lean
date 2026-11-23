import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsCurrent
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

def VarIntAdd.Statement : Prop :=
  ∀ (n k : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (f g : (Fin n → ℂ) → ℝ)
    (φ : Fin k → (Fin n → ℂ) → ℝ),
    J.IsPrime → Continuous f → HasCompactSupport f → Continuous g → HasCompactSupport g →
    (∀ i, SmoothNear (zeroSet J) (φ i)) →
      varInt J k (f + g) φ = varInt J k f φ + varInt J k g φ

end

end GroundTheory.Heights₂.Heights
