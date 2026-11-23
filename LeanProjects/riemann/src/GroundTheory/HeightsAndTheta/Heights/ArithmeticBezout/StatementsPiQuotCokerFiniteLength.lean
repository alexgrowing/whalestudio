import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

def quotToPiMinimalPrimes {B : Type*} [CommRing B] (J : Ideal B) :
    (B ⧸ J) →ₗ[B] ((P : J.minimalPrimes) → B ⧸ (P : Ideal B)) :=
  LinearMap.pi fun P => Submodule.factor P.2.1.2

def PiQuotCokerFiniteLength.Statement : Prop :=
  ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [IsLocalRing B] (J : Ideal B),
    J.IsRadical →
    (∀ Q : Ideal B, Q.IsPrime → J ≤ Q → Q ∈ J.minimalPrimes ∨ Q = IsLocalRing.maximalIdeal B) →
      Function.Injective (quotToPiMinimalPrimes J) ∧
        IsFiniteLength B
          (((P : J.minimalPrimes) → B ⧸ (P : Ideal B)) ⧸ LinearMap.range (quotToPiMinimalPrimes J))

end GroundTheory.Heights₂.Heights
