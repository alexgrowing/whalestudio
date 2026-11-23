import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StTransverseObjects
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open IsLocalRing

universe u

noncomputable section

def CMLengthParameters.Statement : Prop :=
  ∀ (B : Type u) [CommRing B] [IsCohenMacaulayLocalRing B] (P : Ideal B) [P.IsPrime] (d : ℕ) (x : Fin d → B),
    minimalPrimes B = {P} → ringKrullDim (B ⧸ P) = (d : ℕ) →
    Ideal.span (Set.range x) ⊔ P = maximalIdeal B →
      Module.length B (B ⧸ Ideal.span (Set.range x)) =
        Module.length (Localization.AtPrime P) (Localization.AtPrime P)

end

end GroundTheory.Heights₂.Heights
