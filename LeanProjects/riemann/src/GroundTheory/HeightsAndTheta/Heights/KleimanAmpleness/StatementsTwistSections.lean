import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Objects
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

def TwistSections.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (y : Fin (N + 1) → Ω), y ≠ 0 →
    ∀ᶠ n : ℕ in Filter.atTop, (twistSys S y (n : ℤ)).secs = (coordGraded S y).piece (n : ℤ)

end

end GroundTheory.Heights₂.Heights.Kleiman
