import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.FoldBound
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareSeriesSquareIntegrable

open MeasureTheory
open scoped ENNReal NNReal

namespace PI.FoldUnfold

def FoldUnfold : Prop :=
  ∀ (G : Type*) [Group G] [MeasurableSpace G] [MeasurableMul G] (μ : Measure G)
    [μ.IsMulLeftInvariant] (Γ S : Subgroup G) [Countable Γ], S ≤ Γ →
  ∀ (F : Set G), IsFundamentalDomain S F μ →
  ∀ (FΓ : Set G), IsFundamentalDomain Γ FΓ μ →
  ∀ (D : Set G), Formalism.L2.SG.FoldBound.IsRightTransversal Γ S D →
  ∀ (f : G → ℝ≥0∞), Measurable f → (∀ s ∈ S, ∀ y : G, f (s * y) = f y) →
    (∫⁻ x in FΓ, ∑' δ : D, f ((δ : G) * x) ∂μ) = ∫⁻ y in F, f y ∂μ

end PI.FoldUnfold
