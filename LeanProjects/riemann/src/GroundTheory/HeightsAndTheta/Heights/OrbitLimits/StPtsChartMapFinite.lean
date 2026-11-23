import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.RatChartObjects
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

def PtsChartMapFinite.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ)
    (i : (k : K) → ι k) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)),
    IsArithVar P (e + 1) → IsGoodProj P Ψ → ∀ J ∈ (PtsSegreChart.ideal P i).minimalPrimes,
      PtsSegreChart.chartDen Ψ ∉ J ∧
        ∀ y, (RatChart.ratFibre J (PtsSegreChart.chartNum Ψ) (PtsSegreChart.chartDen Ψ) y).Finite

end GroundTheory.Heights₂.Heights
