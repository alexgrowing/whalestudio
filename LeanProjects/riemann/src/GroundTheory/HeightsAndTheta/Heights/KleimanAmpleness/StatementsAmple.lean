import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Objects
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

def AmpleCover.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (H : LineBundle S x) (A : AmpleData S x H) (F : SubSystem S x Ω),
    (∀ (j : Fin (A.r + 1)) (I : Chart x) (y : Ω), y ∈ F.sub I → ∃ e : ℕ,
      y * A.h j ^ e ∈
        Submodule.span (chartRing S x I) (F.secs : Set Ω) * (H.pow (A.m * e)).sub I) →
    F.Generated

def AmpleTwistLocal.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (H : LineBundle S x) (A : AmpleData S x H) (Q : LineBundle S x) (b : ℕ)
    (j : Fin (A.r + 1)),
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ (I : Chart x) (y : Ω), y ∈ (Q.twist (H.pow (b + A.m * n))).sub I →
      ∃ e : ℕ, y * A.h j ^ e ∈
        Submodule.span (chartRing S x I) ((Q.twist (H.pow (b + A.m * n))).secs : Set Ω) *
          (H.pow (A.m * e)).sub I

section Hypotheses

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  (x : Fin (N + 1) → Ω)

variable (k : Type u) [Field k]

end Hypotheses

end

end GroundTheory.Heights₂.Heights.Kleiman
