import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsChartIbpSymm
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsChartIbpSteps
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.ChartCutoffParts
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo Matrix MeasureTheory Filter Topology ChartIntegrationByPartsSymmetry
open scoped ComplexOrder

noncomputable section

theorem ChartIbpSymm.proof (hCut : ChartIbpCutoff.Statement) : ChartIbpSymm.Statement := by
  intro n A B C D T hA hB hC hD hT
  have hF := integrable_pot_mul_maDensity hA hB hC hD hT
  have hG := integrable_pot_mul_maDensity hC hD hA hB hT
  have hFG := hF.sub hG
  have hlim : Tendsto (fun k : ℕ => ∫ y : Fin (n + 1) → ℂ, chartCutoff k y *
      ((hermChartPot A y - hermChartPot B y) *
          maDensity (Fin.cons (fun y' => hermChartPot C y' - hermChartPot D y')
            fun i => hermChartPot (T i)) y -
        (hermChartPot C y - hermChartPot D y) *
          maDensity (Fin.cons (fun y' => hermChartPot A y' - hermChartPot B y')
            fun i => hermChartPot (T i)) y))
      atTop (𝓝 (∫ y : Fin (n + 1) → ℂ,
        ((hermChartPot A y - hermChartPot B y) *
            maDensity (Fin.cons (fun y' => hermChartPot C y' - hermChartPot D y')
              fun i => hermChartPot (T i)) y -
          (hermChartPot C y - hermChartPot D y) *
            maDensity (Fin.cons (fun y' => hermChartPot A y' - hermChartPot B y')
              fun i => hermChartPot (T i)) y))) := by
    refine tendsto_integral_of_dominated_convergence _ (fun k => ?_) hFG.norm (fun k => ?_) ?_
    · exact (contDiff_chartCutoff k 0).continuous.aestronglyMeasurable.mul hFG.aestronglyMeasurable
    · refine Eventually.of_forall fun y => ?_
      rw [norm_mul]
      refine mul_le_of_le_one_left (norm_nonneg _) ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (chartCutoff_nonneg k y)]
      exact chartCutoff_le_one k y
    · refine Eventually.of_forall fun y => ?_
      simpa using (tendsto_chartCutoff y).mul_const
        ((hermChartPot A y - hermChartPot B y) *
            maDensity (Fin.cons (fun y' => hermChartPot C y' - hermChartPot D y')
              fun i => hermChartPot (T i)) y -
          (hermChartPot C y - hermChartPot D y) *
            maDensity (Fin.cons (fun y' => hermChartPot A y' - hermChartPot B y')
              fun i => hermChartPot (T i)) y)
  have h0 := tendsto_nhds_unique hlim (hCut n A B C D T hA hB hC hD hT)
  rw [integral_sub hF hG] at h0
  linarith

end

end GroundTheory.Heights₂.Heights
