import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open IsLocalRing CategoryTheory RingTheory.Sequence

universe u

def AuslanderBuchsbaumDepthLower.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (M : Type u) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Nontrivial M] (ℓ : ℕ) (rs : List R),
    HasProjectiveDimensionLE (ModuleCat.of R M) ℓ → (∀ r ∈ rs, r ∈ maximalIdeal R) → IsWeaklyRegular R rs →
      ∃ ms : List R, (∀ r ∈ ms, r ∈ maximalIdeal R) ∧ IsWeaklyRegular M ms ∧ ms.length = rs.length - ℓ

end GroundTheory.Heights₂.Heights
