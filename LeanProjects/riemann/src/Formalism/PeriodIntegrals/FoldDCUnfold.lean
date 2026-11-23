import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.FoldBound
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareSeriesSquareIntegrable

open MeasureTheory
open scoped ENNReal NNReal

namespace PI.FoldDCUnfold

def FoldDCUnfold : Prop :=
  ∀ (G : Type*) [Group G] [MeasurableSpace G] [MeasurableMul G] (μ : Measure G)
    [μ.IsMulLeftInvariant] (Γ S S' : Subgroup G) [Countable Γ], S ≤ Γ → S' ≤ Γ →
  ∀ (D D' : Set G), Formalism.L2.SG.FoldBound.IsRightTransversal Γ S D →
    Formalism.L2.SG.FoldBound.IsRightTransversal Γ S' D' →
  ∀ (R : Set G), Formalism.L2.SG.PoincareSeriesSquareIntegrable.IsDoubleTransversal Γ S S' R →
  ∀ (Fs : G → Set G), (∀ r ∈ R, IsFundamentalDomain (Formalism.L2.SG.PoincareSeriesSquareIntegrable.stab S S' r) (Fs r) μ) →
  ∀ (FΓ : Set G), IsFundamentalDomain Γ FΓ μ →
  ∀ (g h : G → ℝ≥0∞), Measurable g → Measurable h →
    (∀ s ∈ S, ∀ y : G, g (s * y) = g y) → (∀ s ∈ S', ∀ y : G, h (s * y) = h y) →
    (∫⁻ x in FΓ, (∑' δ : D, g ((δ : G) * x)) * (∑' δ' : D', h ((δ' : G) * x)) ∂μ)
      = ∑' r : R, ∫⁻ x in Fs r, g x * h ((r : G)⁻¹ * x) ∂μ

end PI.FoldDCUnfold
