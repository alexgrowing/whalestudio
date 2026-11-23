import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.SegreChartProjObjects
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StPtsIntegralSegreChartProj
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsArithVar IsGoodProj PBlk)
open ComplexSets

def SegreChartProjFinite.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι)) (e m : ℕ) (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)),
    IsArithVar P (e + 1) → IsGoodProj P Ψ → (∀ w, Ψ w 0 = w i) →
      ∀ J ∈ segreChartComponents P σ i, IsFiniteProjection J (chartProjMatrix σ Ψ)

end GroundTheory.Heights₂.Heights
