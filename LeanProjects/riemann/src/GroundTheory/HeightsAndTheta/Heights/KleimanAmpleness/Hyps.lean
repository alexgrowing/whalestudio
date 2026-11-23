import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsGraphGenTwistBundleZero
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver secOver mIdealOver cechZc quotPart cechMap)
open ReciprocityTheory.ChartRestriction.G.Geo (MRingOver IsMultiHomogIdeal)

def QuotSecsBase.Statement : Prop :=
  ∀ (S : Type) [CommRing S] [IsNoetherianRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type)
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] (Ω : Type) [Field Ω] [Algebra S Ω]
    (y : (Σ k, ι k) → Ω) (k₀ : K) (N : ℕ) (e : ι k₀ ≃ Fin (N + 1)) (J : Ideal (MRingOver S ι))
    (hJ : mIdealOver S y ≤ J),
    IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase S y k₀ → IsMultiHomogIdeal J → ∀ β : K → ℤ,
    ∃ (Q : Kleiman.LineBundle S (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)) (J' : Ideal (Kleiman.Poly S N)),
      (∀ p ∈ J', ∀ d : ℕ, homogeneousComponent d p ∈ J') ∧
      ∀ (c : ℕ), ∀ z'' ∈ cechZc ι (quotPart S J) (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) 0,
        ∃ s : Kleiman.Chart (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) → Ω,
          (∀ I, s I ∈ (Q.twist (Kleiman.twistSys S _ (c : ℤ))).sub I) ∧
          (∀ (I₁ I₂ : Kleiman.Chart (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)), I₁.1 ⊆ I₂.1 →
            s I₁ - s I₂ ∈ ((Q.twist (Kleiman.twistSys S _ (c : ℤ))).twist (Kleiman.idealSys _ J')).sub I₂) ∧
          ∀ t ∈ (Q.twist (Kleiman.twistSys S _ (c : ℤ))).secs,
            (∀ I, t - s I ∈ ((Q.twist (Kleiman.twistSys S _ (c : ℤ))).twist (Kleiman.idealSys _ J')).sub I) →
            ∃ z ∈ cechZc ι (quotPart S (mIdealOver S y)) (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) 0,
              cechMap S ι (Submodule.factor hJ) 0 z = z''

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
