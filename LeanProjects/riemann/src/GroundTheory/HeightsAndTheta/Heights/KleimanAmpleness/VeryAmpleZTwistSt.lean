import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.VeryAmpleCechObj
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u v w

def VeryAmpleZTwist.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (E : Type v) [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
    (F : SubFamily S x E) (H : LineBundle S x) (r : ℕ) (h : Fin (r + 1) → Ω),
    IsVeryAmpleBy H.toSubSystem h → ∀ (a : ℕ) (J : Chart h),
      (Submodule.span (chartRing S h J) {z | ∃ q ∈ twistMod S h (a : ℤ) J,
          ∃ y ∈ secsOnZ F.toSubSystem H.toSubSystem h J, z = q • y}).restrictScalars S =
        secsOnZ (F.twist (H.pow a)) H.toSubSystem h J

end

end GroundTheory.Heights₂.Heights.Kleiman
