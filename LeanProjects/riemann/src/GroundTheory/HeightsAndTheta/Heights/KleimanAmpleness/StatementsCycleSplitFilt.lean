import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.AlgebraMapMemChartRingLine
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w

open Classical in

def CycleSplit.Filt.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (𝔪 : Ideal S), 𝔪.IsMaximal →
    ∀ J : Ideal (Poly S N), (∀ p ∈ J, ∀ d : ℕ, homogeneousComponent d p ∈ J) →
    primeOf (S := S) x ≤ J → 𝔪.map (C : S →+* Poly S N) ≤ J →
    ∃ (n : ℕ) (pp : Fin n → Ideal (Poly S N)) (d : Fin n → ℤ),
      (∀ j, (pp j).IsPrime ∧ (∀ p ∈ pp j, ∀ e : ℕ, homogeneousComponent e p ∈ pp j) ∧ J ≤ pp j) ∧
      (∀ (G : Ideal (Poly S N)) [G.IsPrime], G ∈ J.minimalPrimes →
        (((Finset.univ.filter fun j => pp j = G).card : ℕ) : ℕ∞) = cutMult J G) ∧
      ∀ Q : LineBundle S x, ∀ᶠ c : ℕ in atTop,
        restrLen J (Q.twist (twistSys S x (c : ℤ))) =
          ∑ j, restrLen (pp j) (Q.twist (twistSys S x ((c : ℤ) + d j)))

end

end GroundTheory.Heights₂.Heights.Kleiman
