import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsCurrent
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.SegreChartObjects
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StSegreCoordGoodProj
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open Filter Topology
open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsSmoothHerm IsArithVar IsGoodProj ptsIntegralAt pot segre PBlk oneLine
  isSmoothHerm_oneLine)

def PtsIntegralSegreChartProj.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι)) (e m : ℕ) (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    (L : Fin (e + 1) → HermLine ι) (g : ((Σ k, ι k) → ℂ) → ℝ)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1 + 1) → ℂ))
    (G : (Fin m → ℂ) → ℝ) (Φ : Fin (e + 1) → (Fin m → ℂ) → ℝ),
    IsArithVar P (e + 2) → (∀ j, IsSmoothHerm (L j)) → IsDegZeroSmooth g →
    IsGoodProj P Ψ → (∀ w, Ψ w 0 = w i) →
    (∀ x ∈ segreChartSet P σ i,
      G =ᶠ[𝓝 x] g ∘ chartLift σ i ∧ ∀ j, Φ j =ᶠ[𝓝 x] pot L j ∘ chartLift σ i) →
      ptsIntegralAt P Ψ (pot L) g = ∑ J ∈ segreChartComponents P σ i, varInt J (e + 1) G Φ

end GroundTheory.Heights₂.Heights
