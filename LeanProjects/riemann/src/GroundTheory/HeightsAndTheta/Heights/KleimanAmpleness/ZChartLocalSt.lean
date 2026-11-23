import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.VeryAmpleCechObj
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u v w

def ZChartLocal.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (E : Type v) [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
    (G : SubFamily S x E) (H : LineBundle S x) (r : ℕ) (h : Fin (r + 1) → Ω),
    (∀ l, h l ∈ H.secs) → ∀ (J : Chart h) (j : Fin (r + 1)), j ∈ J.1 →
    ∀ (b : Ω), b ∈ ampleRing H.toSubSystem 1 (h j) → ∀ K : Chart x,
      (∀ I : Chart x, ∃ e : ℕ,
        b ^ e * (xProd I ^ K.1.card / xProd K ^ I.1.card) ∈ ampleChart H.toSubSystem 1 (h j) I) →
      ∀ j₀ ∈ K.1, ∀ I I' : Chart x, I'.1 = insert j₀ I.1 →
        ∀ z ∈ secsOnZChart G.toSubSystem H.toSubSystem h I' J,
          ∃ e : ℕ, b ^ e • z ∈ secsOnZChart G.toSubSystem H.toSubSystem h I J

end

end GroundTheory.Heights₂.Heights.Kleiman
