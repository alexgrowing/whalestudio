import Mathlib

universe u

namespace PI

def MiracleFlat : Prop :=
  ∀ (A B : Type u) [CommRing A] [CommRing B] [IsRegularLocalRing A]
    [IsLocalRing B] [IsNoetherianRing B] [Algebra A B] [IsLocalHom (algebraMap A B)],
    (∃ rs : List B, RingTheory.Sequence.IsRegular B rs ∧
      (∀ r ∈ rs, r ∈ IsLocalRing.maximalIdeal B) ∧
      (rs.length : WithBot ℕ∞) = ringKrullDim B) →
    ringKrullDim B = ringKrullDim A +
      ringKrullDim (B ⧸ (IsLocalRing.maximalIdeal A).map (algebraMap A B)) →
    Module.Flat A B

end PI
