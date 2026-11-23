import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StGoodChartModel
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StSegreChartZeroSet
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsMultiHomogIdeal PBlk)
open ComplexSets

def GoodChartZeroSet.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e m : ℕ)
    (σ : Fin m ≃ ((k : K) → ι k)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)),
    IsMultiHomogIdeal P → zeroSet (projChartIdeal P σ Ψ) = projChartSet P σ Ψ

end GroundTheory.Heights₂.Heights
