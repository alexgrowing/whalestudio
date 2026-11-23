import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GenericPointSectionHypotheses
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

def GenericRestrLen.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsDomain S] (F : Type u) [Field F] [Algebra S F]
    [IsFractionRing S F] (Ω : Type w) [Field Ω] [Algebra S Ω] [Algebra F Ω] [IsScalarTower S F Ω]
    (N : ℕ) (x : Fin (N + 1) → Ω) (Q : SubSystem S x Ω) (qq : Ideal (Poly S N)),
    (∀ p ∈ qq, ∀ d : ℕ, homogeneousComponent d p ∈ qq) →
    restrLen (qq.map (MvPolynomial.map (algebraMap S F))) (Q.extend F) =
      (Module.finrank S (Q.secs ⧸ ((Q.twist (idealSys x qq)).secs).comap Q.secs.subtype) : ℤ)

end

end GroundTheory.Heights₂.Heights.Kleiman
