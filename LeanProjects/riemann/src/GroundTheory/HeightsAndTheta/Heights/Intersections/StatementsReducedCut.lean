import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

def ReducedCutLength.Statement : Prop :=
  ∀ (T : Type) [CommRing T] [IsNoetherianRing T] (I : Ideal T) (x : T) (Q : Ideal T) [Q.IsPrime],
    I.IsRadical → (∀ p ∈ I.minimalPrimes, x ∉ p) → Q ∈ (I ⊔ Ideal.span {x}).minimalPrimes →
    Module.length (Localization.AtPrime Q)
        (LocalizedModule Q.primeCompl (T ⧸ (I ⊔ Ideal.span {x}))) =
      ∑ᶠ p ∈ I.minimalPrimes, Module.length (Localization.AtPrime Q)
        (LocalizedModule Q.primeCompl (T ⧸ (p ⊔ Ideal.span {x})))

end GroundTheory.Heights₂.Heights.Inter
