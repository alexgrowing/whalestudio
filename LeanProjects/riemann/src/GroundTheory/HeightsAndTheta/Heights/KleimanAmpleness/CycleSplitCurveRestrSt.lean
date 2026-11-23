import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GenericPointSectionHypotheses
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w

def CycleSplit.Curve.Restr.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (pp : Ideal (Poly S N)), pp.IsPrime →
    (∀ p ∈ pp, ∀ d : ℕ, homogeneousComponent d p ∈ pp) → primeOf (S := S) x ≤ pp →
    ∀ (j : Fin (N + 1)) (hj : x j ≠ 0), (X j : Poly S N) ∉ pp →
    ∀ (K' : Type w) [Field K'] [Algebra S K'] (ψ : chartRing S x (singleChart hj) →ₐ[S] K'),
      RingHom.ker ψ = chartPrime pp hj →
      ∀ (hxy : ∀ i, ψ (ratio hj i) ≠ 0 → x i ≠ 0) (Q : LineBundle S x)
        (Q' : LineBundle S (fun i => ψ (ratio hj i))) (r : Ω → K'),
        RestrictData Q.toSubSystem hxy Q'.toSubSystem r →
        ∀ᶠ c : ℕ in atTop,
          restrLen pp (Q.toSubSystem.twist (twistSys S x (c : ℤ))) =
            restrLen pp (Q'.toSubSystem.twist (twistSys S (fun i => ψ (ratio hj i)) (c : ℤ)))

end

end GroundTheory.Heights₂.Heights.Kleiman
