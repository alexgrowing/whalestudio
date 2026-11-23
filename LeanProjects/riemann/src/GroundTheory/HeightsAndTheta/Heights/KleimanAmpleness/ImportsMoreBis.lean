import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PDomination
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

def DomRingTwist.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (Ω : Type) [Field Ω] [Algebra S Ω] (N N' : ℕ) (x : Fin (N + 1) → Ω)
    (x' : Fin (N' + 1) → Ω) (i : Fin (N + 1)), x i ≠ 0 → ∀ b ∈ Kleiman.domRing S x x' i,
      ∃ c : ℕ, b * x i ^ c ∈ Kleiman.pullSecs x' (Kleiman.twistSys S x (c : ℤ))

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
