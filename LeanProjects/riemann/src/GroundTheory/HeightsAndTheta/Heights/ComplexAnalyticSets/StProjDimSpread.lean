import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open CategoryTheory

def ProjDimSpread.Statement : Prop :=
  ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I P : Ideal R) [P.IsPrime] (ℓ : ℕ),
    HasProjectiveDimensionLE (ModuleCat.of (Localization.AtPrime P)
      (Localization.AtPrime P ⧸ I.map (algebraMap R (Localization.AtPrime P)))) ℓ →
    ∃ g : R, g ∉ P ∧ ∀ (Q : Ideal R) [Q.IsPrime], g ∉ Q →
      HasProjectiveDimensionLE (ModuleCat.of (Localization.AtPrime Q)
        (Localization.AtPrime Q ⧸ I.map (algebraMap R (Localization.AtPrime Q)))) ℓ

end GroundTheory.Heights₂.Heights
