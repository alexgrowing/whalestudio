import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StRegLelongMono
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix ComplexSets

noncomputable section

def VarLelongMono.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (d + 1)) (Fin n) ℂ)
    (x : Fin n → ℂ) (r s : ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → IsFiniteProjection J A →
    0 < r → r ≤ s →
      s ^ (2 * (d + 1)) * ∫ y, chartDens J A ((euclBall x r).indicator fun _ => 1) (fun _ => euclPot) y ≤
        r ^ (2 * (d + 1)) * ∫ y, chartDens J A ((euclBall x s).indicator fun _ => 1) (fun _ => euclPot) y

end

end GroundTheory.Heights₂.Heights
