import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Statements
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.AlgebraMapMemChartRingLine
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

def TwistSplit.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (M₀ : FinGradedSub (S := S) (x := x) Ω) (G B : SubSystem S x Ω) (r : ℕ)
    (η : Fin (r + 1) → Ω), (∀ I, M₀.tilde 0 I = G.sub I) →
    (∀ j, η j ∈ B.secs) → (∀ I, Submodule.span (chartRing S x I) (Set.range η) = B.sub I) →
    ∃ (M : Type w) (_ : AddCommGroup M) (_ : Module (Poly (MvPolynomial (Fin (r + 1)) S) N) M)
      (_ : Module (MvPolynomial (Fin (r + 1)) S) M)
      (_ : IsScalarTower (MvPolynomial (Fin (r + 1)) S) (Poly (MvPolynomial (Fin (r + 1)) S) N) M)
      (𝓜 : GradedPMod (MvPolynomial (Fin (r + 1)) S) N M),
      Module.Finite (Poly (MvPolynomial (Fin (r + 1)) S) N) M ∧
      ∀ (b : ℕ) (c : ℤ) (i : ℕ),
        ∃ (ι : ((G.twist (B.pow b)).twist (twistSys S x c)).H i →+ cohom 𝓜 i c)
          (π : cohom 𝓜 i c →+ ((G.twist (B.pow b)).twist (twistSys S x c)).H i), ∀ z, π (ι z) = z

section Hypotheses

variable (k : Type u) [Field k] (N : ℕ)

end Hypotheses

end

end GroundTheory.Heights₂.Heights.Kleiman
