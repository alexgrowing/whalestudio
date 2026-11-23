import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CellHOfCellSec
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

def CechContract.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (Ω : Type) [Field Ω] [Algebra S Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (G : Kleiman.Chart x → Submodule S Ω) (J₀ : Kleiman.Chart x),
    J₀.1.card = 1 →
    (∀ J J' : Kleiman.Chart x, J.1 ⊆ J'.1 → G J ≤ G J') →
    (∀ J J' : Kleiman.Chart x, J'.1 = J₀.1 ∪ J.1 → G J' = G J) →
    CechAugExact S G (G J₀)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
