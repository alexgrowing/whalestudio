import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.AevalEqZeroOfMemSatIdealModel
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver)
open ReciprocityTheory.ChartRestriction.G.Geo (MRingOver)

def QuotChartLift.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra S Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (N : ℕ) (e : ι k₀ ≃ Fin (N + 1))
    (J : Ideal (MRingOver S ι)) (γ : K → ℤ) (w : (∀ k, ι k) → Ω),
    IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase S y k₀ →
    (∀ d : ∀ k, ι k, (∀ k, y ⟨k, d k⟩ ≠ 0) → w d * genInv y γ d ∈ chartRingOver S y d) →
    (∀ d d' : ∀ k, ι k, (∀ k, y ⟨k, d k⟩ ≠ 0) → (∀ k, y ⟨k, d' k⟩ ≠ 0) →
      (w d - w d') * genInv y γ d ∈
        Submodule.span ↥(chartRingOver S y d ⊔ chartRingOver S y d') (dehom S y J d)) →
    ∀ i, baseVec y k₀ e i ≠ 0 → ∃ s : Ω, ∀ d : ∀ k, ι k, (∀ k, y ⟨k, d k⟩ ≠ 0) →
      s * genInv y γ d ∈ overRing (S := S) y k₀ e d i ∧
        (s - w d) * genInv y γ d ∈ Submodule.span ↥(overRing (S := S) y k₀ e d i) (dehom S y J d)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
