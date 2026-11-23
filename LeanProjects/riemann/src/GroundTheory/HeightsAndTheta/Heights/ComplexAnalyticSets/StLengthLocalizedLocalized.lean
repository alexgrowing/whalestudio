import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

universe u v

def LengthLocalizedLocalized.Statement : Prop :=
  ∀ (B : Type u) [CommRing B] (P Q : Ideal B) [P.IsPrime] [Q.IsPrime]
    [(P.map (algebraMap B (Localization.AtPrime Q))).IsPrime]
    (M : Type v) [AddCommGroup M] [Module B M],
    P ≤ Q →
      Module.length (Localization.AtPrime (P.map (algebraMap B (Localization.AtPrime Q))))
          (LocalizedModule (P.map (algebraMap B (Localization.AtPrime Q))).primeCompl
            (LocalizedModule Q.primeCompl M)) =
        Module.length (Localization.AtPrime P) (LocalizedModule P.primeCompl M)

theorem LengthLocalizedLocalized.map_isPrime (B : Type u) [CommRing B] (P Q : Ideal B) [hP : P.IsPrime]
    [Q.IsPrime] (h : P ≤ Q) : (P.map (algebraMap B (Localization.AtPrime Q))).IsPrime :=
  IsLocalization.isPrime_of_isPrime_disjoint Q.primeCompl _ P hP
    (Set.disjoint_left.mpr fun _ hx hxP => hx (h hxP))

end GroundTheory.Heights₂.Heights
