import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.AlgebraMapMemChartRingLine
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

def SubFamilyTwist.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (E : Type v) [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
    (F : SubFamily S x E) (Q : LineBundle S x), (∀ I, (F.sub I).FG) →
    ∃ G : SubFamily S x E, G.toSubSystem = F.toSubSystem.twist Q.toSubSystem ∧ ∀ I, (G.sub I).FG

end

end GroundTheory.Heights₂.Heights.Kleiman
