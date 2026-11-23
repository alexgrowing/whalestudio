import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open IsLocalRing CategoryTheory RingTheory.Sequence

universe u

def AuslanderBuchsbaumProjDimUpper.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (M : Type u) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Nontrivial M] (n d : ℕ) (ms : List R),
    HasProjectiveDimensionLE (ModuleCat.of R M) n →
    (∀ rs : List R, (∀ r ∈ rs, r ∈ maximalIdeal R) → IsWeaklyRegular R rs → rs.length ≤ d) →
    (∀ r ∈ ms, r ∈ maximalIdeal R) → IsWeaklyRegular M ms →
      HasProjectiveDimensionLE (ModuleCat.of R M) (d - ms.length)

end GroundTheory.Heights₂.Heights
