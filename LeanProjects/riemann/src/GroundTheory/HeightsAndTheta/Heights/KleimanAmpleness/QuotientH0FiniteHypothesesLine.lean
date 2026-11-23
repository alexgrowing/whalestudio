import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GenericPointSectionHypotheses
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

def QuotientH0Finite.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (E : Type v) [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
    (F G : SubSystem S x E), (∀ I, G.sub I ≤ F.sub I) →
    Module.Finite S (F.H 0) → Module.Finite S (G.H 1) → Module.Finite S (SubSystem.quotH F G 0)

end

end GroundTheory.Heights₂.Heights.Kleiman
