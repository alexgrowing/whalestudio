import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Regularisation.Statements
import GroundTheory.HeightsAndTheta.Heights.Regularisation.ProjLineChartsNotSubsetBall
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular

open MeasureTheory Filter Topology
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsPosPot maMeasure)
open GroundTheory.Heights₂.Heights.Regular (PotentialCharts)

noncomputable section

def ChartMongeAmpereL1Measure.Statement : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
    (D : ℕ) (A : FinHolAtlas D X) (P : PotentialCharts A) (om : LocPot X),
    IsPotential A om → IsPosPot A om → ∀ (g : ℝ → X → ℝ) (t₀ : ℝ), 0 < t₀ →
      (∀ k : Fin P.N,
        (∀ t : ℝ, 0 < t → t < t₀ → IntegrableOn (fun y => g t ((P.chart k).symm y)) (P.chartMid k)) ∧
        Tendsto (fun t => ∫ y in P.chartMid k, |g t ((P.chart k).symm y)|) (𝓝[>] 0) (𝓝 0)) →
      (∀ t : ℝ, 0 < t → t < t₀ → Integrable (g t) (maMeasure A (fun _ : Fin D => om))) ∧
        Tendsto (fun t => ∫ x, |g t x| ∂(maMeasure A (fun _ : Fin D => om))) (𝓝[>] 0) (𝓝 0)

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular
