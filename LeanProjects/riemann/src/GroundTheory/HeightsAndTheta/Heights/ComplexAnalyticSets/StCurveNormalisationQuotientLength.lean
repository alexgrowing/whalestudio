import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCurveNormalisationLength
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

def CurveNormalisationQuotientLength.Statement : Prop :=
  ∀ (n : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ), IsRadicalAt I q →
    ringKrullDim (curveLocalRing I q) = 1 →
    Module.length (curveLocalRing I q)
        (curveNormalisation I q ⧸
          LinearMap.range (Algebra.linearMap (curveLocalRing I q) (curveNormalisation I q))) ≠ ⊤

end GroundTheory.Heights₂.Heights
