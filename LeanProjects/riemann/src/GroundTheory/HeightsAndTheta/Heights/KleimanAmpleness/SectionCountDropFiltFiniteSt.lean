import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GenericPointSectionHypotheses
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

def SectionCount.Drop.Filt.Finite.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (Q : LineBundle S x) (pp : Ideal (Poly S N)) (c : ℤ), pp.IsPrime →
    (∀ f ∈ pp, ∀ d : ℕ, homogeneousComponent d f ∈ pp) → primeOf (S := S) x ≤ pp →
    Module.Finite S (SubSystem.quotH (Q.twist (twistSys S x c))
      ((Q.twist (twistSys S x c)).twist (idealSys x pp)) 0)

end

end GroundTheory.Heights₂.Heights.Kleiman
