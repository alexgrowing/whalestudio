import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StTransverseObjects
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial CategoryTheory

def CMProjDimCriterion.Statement : Prop :=
  ∀ (n : ℕ) (I Q : Ideal (MvPolynomial (Fin n) ℂ)) [Q.IsPrime], I ≤ Q →
    (IsCohenMacaulayLocalRing (Localization.AtPrime Q ⧸
        I.map (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime Q))) ↔
      ∃ ℓ : ℕ, HasProjectiveDimensionLE (ModuleCat.of (Localization.AtPrime Q) (Localization.AtPrime Q ⧸
          I.map (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime Q)))) ℓ ∧
        (ℓ : ℕ∞) ≤ (I.map (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime Q))).height)

end GroundTheory.Heights₂.Heights
