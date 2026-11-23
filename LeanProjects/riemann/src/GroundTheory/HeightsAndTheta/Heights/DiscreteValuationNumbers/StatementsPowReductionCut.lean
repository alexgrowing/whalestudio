import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

universe u

section Lemmas

def PowSpanFinrankBounded.Statement : Prop :=
  ∀ (A : Type u) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A],
    ringKrullDim A = 1 → ∀ I : Ideal A, ∃ e : ℕ, ∀ n : ℕ, (I ^ n).spanFinrank ≤ e

def PrincipalReductionOfBoundedGens.Statement : Prop :=
  ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (I : Ideal A),
    (∃ e : ℕ, ∀ n : ℕ, (I ^ n).spanFinrank ≤ e) →
      ∃ k : ℕ, 1 ≤ k ∧ ∃ y ∈ I ^ k, ∃ n : ℕ, I ^ (n + k) = Ideal.span {y} * I ^ n

end Lemmas

section Examples

end Examples

end GroundTheory.Heights₂.Heights.NumbersDVR
