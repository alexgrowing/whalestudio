import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open IsLocalRing RingTheory.Sequence

universe u

def RegularSequenceLengthLeDim.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (rs : List R),
    (∀ r ∈ rs, r ∈ maximalIdeal R) → IsWeaklyRegular R rs → (rs.length : WithBot ℕ∞) ≤ ringKrullDim R

end GroundTheory.Heights₂.Heights
