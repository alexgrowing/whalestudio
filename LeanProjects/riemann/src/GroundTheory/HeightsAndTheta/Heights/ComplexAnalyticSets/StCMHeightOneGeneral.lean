import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StTransverseObjects
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

def CMHeightOneGeneral.Statement : Prop :=
  ∀ (n : ℕ) (J W : Ideal (MvPolynomial (Fin n) ℂ)) (g : MvPolynomial (Fin n) ℂ),
    J.IsPrime → g ∉ J → W ∈ (J ⊔ Ideal.span {g}).minimalPrimes →
      ∃ f : MvPolynomial (Fin n) ℂ, f ∉ W ∧ ∀ q ∈ zeroSet W, eval q f ≠ 0 → IsCohenMacaulayAt J q

end GroundTheory.Heights₂.Heights
