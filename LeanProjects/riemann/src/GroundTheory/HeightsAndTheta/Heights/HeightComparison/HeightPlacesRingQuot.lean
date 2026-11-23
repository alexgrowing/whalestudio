import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightPlacesRing
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField

def PlacesRingQuot.Statement : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (S : Set (FinitePlace L)), S.Finite →
    ∀ g : placesRing S, g ≠ 0 →
      Real.log (Nat.card (placesRing S ⧸ Ideal.span {g})) = ∑ᶠ w ∈ S, -Real.log (w (g : L))

example : ∃ (S : Set (FinitePlace ℚ)) (g : placesRing S), S.Finite ∧ g ≠ 0 :=
  ⟨∅, 1, Set.finite_empty, one_ne_zero⟩

end GroundTheory.Heights₂.Heights
