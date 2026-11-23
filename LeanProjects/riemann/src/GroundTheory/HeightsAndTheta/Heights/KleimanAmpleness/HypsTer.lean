import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.AevalEqZeroOfMemSatIdealModel
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver secOver mIdealOver cechZc quotPart cechMap CechC)
open ReciprocityTheory.ChartRestriction.G.Geo (MRingOver IsMultiHomogIdeal)

def QuotCocycleValues.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)]
    [∀ k, LinearOrder (ι k)] (Ω : Type) [Field Ω] [Algebra S Ω] (y : (Σ k, ι k) → Ω) (J : Ideal (MRingOver S ι))
    (hJ : mIdealOver S y ≤ J) (γ : K → ℤ),
    ∀ z'' ∈ cechZc ι (quotPart S J) γ 0,
      ∃ w : (∀ k, ι k) → Ω,
        (∀ d : ∀ k, ι k, (∀ k, y ⟨k, d k⟩ ≠ 0) → w d * genInv y γ d ∈ chartRingOver S y d) ∧
        (∀ d d' : ∀ k, ι k, (∀ k, y ⟨k, d k⟩ ≠ 0) → (∀ k, y ⟨k, d' k⟩ ≠ 0) →
          (w d - w d') * genInv y γ d ∈
            Submodule.span ↥(chartRingOver S y d ⊔ chartRingOver S y d') (dehom S y J d)) ∧
        ∀ t ∈ secOver S y γ,
          (∀ d : ∀ k, ι k, (∀ k, y ⟨k, d k⟩ ≠ 0) →
            (t - w d) * genInv y γ d ∈ Submodule.span ↥(chartRingOver S y d) (dehom S y J d)) →
          ∃ z ∈ cechZc ι (quotPart S (mIdealOver S y)) γ 0, cechMap S ι (Submodule.factor hJ) 0 z = z''

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
