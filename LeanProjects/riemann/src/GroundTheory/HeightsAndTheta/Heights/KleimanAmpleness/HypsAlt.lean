import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.AevalEqZeroOfMemSatIdealModel
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver)
open ReciprocityTheory.ChartRestriction.G.Geo (MRingOver)

def QuotIdealSub.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra S Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (N : ℕ) (e : ι k₀ ≃ Fin (N + 1))
    (J : Ideal (MRingOver S ι)) (hy : IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase S y k₀) (β : K → ℤ) (c : ℤ)
    (I : Kleiman.Chart (baseVec y k₀ e)) (u : Ω),
    (∀ d : ∀ k, ι k, (∀ k, y ⟨k, d k⟩ ≠ 0) →
      u * genInv y (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) d ∈
        Submodule.span ↥(chartRingOver S y d ⊔ Kleiman.chartRing S (baseVec y k₀ e) I) (dehom S y J d)) →
    u ∈ (((TranslateEq.ofSecond (bundleOfDeg (e := e) hy β)).twist (Kleiman.twistSys S (baseVec y k₀ e) c)).twist
      (Kleiman.idealSys (baseVec y k₀ e) (satIdeal S y k₀ e J))).sub I

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
