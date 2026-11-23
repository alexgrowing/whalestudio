import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StTransverseObjects
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

def CMGeneralPoint.Statement : Prop :=
  ∀ (n : ℕ) (I W : Ideal (MvPolynomial (Fin n) ℂ)), W ∈ I.minimalPrimes →
    ∃ f : MvPolynomial (Fin n) ℂ, f ∉ W ∧ ∀ q ∈ zeroSet W, eval q f ≠ 0 →
      (∀ W' ∈ I.minimalPrimes, q ∈ zeroSet W' → W' = W) ∧ IsCohenMacaulayAt I q

end GroundTheory.Heights₂.Heights
