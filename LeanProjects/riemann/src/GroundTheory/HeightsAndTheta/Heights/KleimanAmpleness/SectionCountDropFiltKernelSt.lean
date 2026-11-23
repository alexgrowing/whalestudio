import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GenericPointSectionHypotheses
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

def SectionCount.Drop.Filt.Kernel.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (j : Fin (N + 1)) (b : ℕ) (F : SubSystem S x Ω), x j ≠ 0 →
    (∀ t ∈ (F.twist (twistSys S x (-(b : ℤ)))).secs, x j ^ b * t ∈ F.secs) ∧
    ∀ s ∈ (F.twist (idealSys x (primeOf (S := S) x ⊔
        zeroIdeal (twistSys S x (b : ℤ)) (x j ^ b)))).secs,
      ∃ t ∈ (F.twist (twistSys S x (-(b : ℤ)))).secs, s = x j ^ b * t

end

end GroundTheory.Heights₂.Heights.Kleiman
