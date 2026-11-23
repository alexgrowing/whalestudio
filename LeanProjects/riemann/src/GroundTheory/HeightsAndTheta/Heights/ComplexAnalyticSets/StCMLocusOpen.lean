import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StTransverseObjects
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

def CMLocusOpen.Statement : Prop :=
  ∀ (n : ℕ) (I P : Ideal (MvPolynomial (Fin n) ℂ)) [P.IsPrime], I ≤ P →
    IsCohenMacaulayLocalRing (Localization.AtPrime P ⧸
      I.map (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime P))) →
    ∃ g : MvPolynomial (Fin n) ℂ, g ∉ P ∧ ∀ (Q : Ideal (MvPolynomial (Fin n) ℂ)) [Q.IsPrime], I ≤ Q → g ∉ Q →
      IsCohenMacaulayLocalRing (Localization.AtPrime Q ⧸
        I.map (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime Q)))

end GroundTheory.Heights₂.Heights
