import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.AlgebraMapMemChartRingLine
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w

def CycleSplit.Filt.Step.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (𝔪 : Ideal S), 𝔪.IsMaximal →
    ∀ (K pp : Ideal (Poly S N)) (g : Poly S N) (e : ℕ),
    (∀ f ∈ K, ∀ d : ℕ, homogeneousComponent d f ∈ K) → primeOf (S := S) x ≤ K →
    𝔪.map (C : S →+* Poly S N) ≤ K → g.IsHomogeneous e →
    (∀ f ∈ pp, ∀ d : ℕ, homogeneousComponent d f ∈ pp) → (∀ f, f ∈ pp ↔ f * g ∈ K) →
    ∀ Q : LineBundle S x, ∀ᶠ c : ℕ in atTop,
      restrLen K (Q.twist (twistSys S x (c : ℤ))) =
        restrLen (K ⊔ Ideal.span {g}) (Q.twist (twistSys S x (c : ℤ))) +
          restrLen pp (Q.twist (twistSys S x ((c : ℤ) - e)))

end

end GroundTheory.Heights₂.Heights.Kleiman
