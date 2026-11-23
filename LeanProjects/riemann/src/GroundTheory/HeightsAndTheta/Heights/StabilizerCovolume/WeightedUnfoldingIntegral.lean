import Mathlib
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.WeightedUnfolding
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open NumberField MeasureTheory GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FiniteCovolume
open scoped ENNReal Matrix

def WeightedUnfoldingIntegral.Statement : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (V : HermSpace E N)
    (M : Majorant V) (c : InfinitePlace E → ℝ), (∀ w, 0 < c w) →
    ∀ (L : Submodule (𝓞 E) (Fin N → E)) (v₀ : Fin N → E),
    IsLattice L → (∀ x ∈ L, ∀ y ∈ L, IsIntegral ℤ (V.h x y)) →
    v₀ ∈ L → v₀ ≠ 0 → V.h v₀ v₀ = 0 →
    ∀ μ : Measure (RealPts V), μ.IsHaarMeasure →
    ∃ s : Set (RealPts V), MeasurableSet s ∧ IsFundamentalDomain (gammaVecInf V L v₀) s μ ∧
      (∫⁻ g in s, wBelowInd M c v₀ 1 g ∂μ) < ⊤ ∧
      ∀ t : ℝ, 0 < t → (∫⁻ g in s, wBelowInd M c v₀ t g ∂μ) =
        ENNReal.ofReal t ^ (2 * fDeg E * (N - 1)) * ∫⁻ g in s, wBelowInd M c v₀ 1 g ∂μ

end GroundTheory.Heights₂.Heights.NineStatements
