import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StVarLelongMono
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StRegLelongAnnulus
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix ComplexSets

noncomputable section

def VarLelongAnnulus.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (d + 1)) (Fin n) ℂ)
    (x : Fin n → ℂ) (r s : ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → IsFiniteProjection J A →
    0 < r → r ≤ s →
      r ^ (2 * (d + 1)) * (∫ y, chartDens J A ((euclBall x s).indicator fun _ => 1) (fun _ => euclPot) y) -
        s ^ (2 * (d + 1)) * (∫ y, chartDens J A ((euclBall x r).indicator fun _ => 1) (fun _ => euclPot) y) =
      r ^ (2 * (d + 1)) * s ^ (2 * (d + 1)) *
        ∫ y, chartDens J A ((euclBall x s \ euclBall x r).indicator fun _ => 1) (fun _ => logDistSq x) y

end

end GroundTheory.Heights₂.Heights
