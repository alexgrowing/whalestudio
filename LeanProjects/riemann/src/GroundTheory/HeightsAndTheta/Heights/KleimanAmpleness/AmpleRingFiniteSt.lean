import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Objects
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

def AmpleRingFinite.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (N : ℕ) (Ω : Type) [Field Ω] [Algebra S Ω] (x : Fin (N + 1) → Ω)
    (H : LineBundle S x) (D : AmpleData S x H) (j : Fin (D.r + 1)), D.h j ≠ 0 →
      ∃ (r : ℕ) (b : Fin r → Ω), (∀ l, b l ∈ ampleRing H.toSubSystem D.m (D.h j)) ∧
        ampleRing H.toSubSystem D.m (D.h j) ⊆ Submodule.span (ampleBase (S := S) D.h j) (Set.range b)

end GroundTheory.Heights₂.Heights.Kleiman
