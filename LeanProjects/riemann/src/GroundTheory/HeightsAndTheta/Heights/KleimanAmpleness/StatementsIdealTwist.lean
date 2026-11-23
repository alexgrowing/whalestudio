import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.AlgebraMapMemChartRingLine
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

def IdealTwistFamily.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (Q : LineBundle S x) (J' : Ideal (Poly S N)),
    (∀ p ∈ J', ∀ d : ℕ, homogeneousComponent d p ∈ J') →
    ∃ F : SubFamily S x Ω, F.toSubSystem = Q.twist (idealSys x J') ∧ ∀ I, (F.sub I).FG

end

end GroundTheory.Heights₂.Heights.Kleiman
