import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.SegreChartProjObjects
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StPtsIntegralSegreChartProj
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MeasureTheory
open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsSmoothHerm IsArithVar PBlk oneLine isSmoothHerm_oneLine)
open ComplexSets

def SegreChartAbsIntegrable.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι)) (e m : ℕ) (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    (L : Fin e → HermLine ι) (g : ((Σ k, ι k) → ℂ) → ℝ),
    IsArithVar P (e + 1) → (∀ j, IsSmoothHerm (L j)) → IsDegZeroSmooth g →
      ∀ J ∈ segreChartComponents P σ i, ∀ A : Matrix (Fin e) (Fin m) ℂ, IsFiniteProjection J A →
        Integrable (chartAbsDens J A (chartWeight σ i g) (chartPot σ i L))

end GroundTheory.Heights₂.Heights
