import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.VeryAmpleCechObj
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open Filter

noncomputable section

universe u v w

def VeryAmpleZExtend.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (E : Type v) [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
    (F : SubFamily S x E) (H : SubSystem S x Ω) (r : ℕ) (h : Fin (r + 1) → Ω), (∀ l, h l ∈ H.secs) →
    ∀ (J : Chart h) (j : Fin (r + 1)), j ∈ J.1 → ∀ c ∈ ampleRing H 1 (h j), ∀ K : Chart x,
      (∀ I : Chart x, ∃ e : ℕ, c ^ e * (xProd I ^ K.1.card / xProd K ^ I.1.card) ∈ ampleChart H 1 (h j) I) →
      ∀ f ∈ F.sub K, ∀ᶠ M in atTop, c ^ M • f ∈ secsOnZ F.toSubSystem H h J

def VeryAmpleZChartSpan.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (E : Type v) [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
    (F : SubSystem S x E) (H : SubSystem S x Ω) (r : ℕ) (h : Fin (r + 1) → Ω), (∀ l, h l ∈ H.secs) →
    ∀ (I : Chart x) (J : Chart h) (g : Finset E), F.sub I ≤ Submodule.span (chartRing S x I) (g : Set E) →
      ∀ e ∈ secsOnZChart F H h I J, ∃ β : E → Ω,
        (∀ y ∈ g, β y ∈ ampleChart H J.1.card (xProd J) I) ∧ e = ∑ y ∈ g, β y • y

def VeryAmpleZChartRing.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (H : LineBundle S x) (r : ℕ) (h : Fin (r + 1) → Ω), IsVeryAmpleBy H.toSubSystem h →
    ∀ (J : Chart h) (j : Fin (r + 1)), j ∈ J.1 → ∀ c ∈ ampleRing H.toSubSystem 1 (h j), ∀ K : Chart x,
      (∀ I : Chart x, ∃ e : ℕ,
        c ^ e * (xProd I ^ K.1.card / xProd K ^ I.1.card) ∈ ampleChart H.toSubSystem 1 (h j) I) →
      ∀ α ∈ ampleChart H.toSubSystem J.1.card (xProd J) K, ∀ᶠ M in atTop, c ^ M * α ∈ chartRing S h J

theorem genericPt_one_zero_ne_zero (k : Type u) [Field k] : genericPt k 1 0 ≠ 0 := by
  intro h0
  have := (map_eq_zero_iff _ (IsFractionRing.injective (Poly k 1) (FractionRing (Poly k 1)))).mp h0
  exact MvPolynomial.X_ne_zero _ this

def lineChartZero (k : Type u) [Field k] : Chart (genericPt k 1) := singleChart (genericPt_one_zero_ne_zero k)

end

end GroundTheory.Heights₂.Heights.Kleiman
