import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Objects
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

def AmpleAffineGen.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (H : LineBundle S x) (A : AmpleData S x H) (Q : LineBundle S x) (b : ℕ)
    (j : Fin (A.r + 1)), A.h j ≠ 0 →
    ∃ (p : ℕ) (s : Fin p → Ω),
      (∀ (t : Fin p) (I : Chart x), ∃ k : ℕ,
        s t * A.h j ^ k ∈ (Q.twist (H.pow (b + A.m * k))).sub I) ∧
      ∀ (I : Chart x) (z : Ω) (k : ℕ), z * A.h j ^ k ∈ (Q.twist (H.pow (b + A.m * k))).sub I →
        ∃ (e : ℕ) (g : Fin p → Ω), (∀ t, g t * A.h j ^ e ∈ (H.pow (A.m * e)).sub I) ∧
          z = ∑ t, g t * s t

section Hypotheses

variable (k : Type u) [Field k]

end Hypotheses

end

end GroundTheory.Heights₂.Heights.Kleiman
