import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FubiniStudyInvariance.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open scoped LinearAlgebra.Projectivization ComplexConjugate Matrix ENNReal
open MeasureTheory Set MvPolynomial

noncomputable section

namespace FSInv

open CP

theorem FormIntegral.proof (hC : ChartIndep.Statement) : FormIntegral.Statement := by
  intro N i g hg
  rw [hC N i] at hg ⊢
  rw [integral_map (measurable_chartInv i).aemeasurable hg, fsChartMeasure]
  have hd : (fun z => ENNReal.ofReal (fsVolumeDensity (N := N) i z)) =
      fun z => (((fsVolumeDensity (N := N) i z).toNNReal : NNReal) : ℝ≥0∞) := rfl
  rw [hd, integral_withDensity_eq_integral_smul (measurable_fsVolumeDensity i).real_toNNReal]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only [NNReal.smul_def, Real.coe_toNNReal _ (fsVolumeDensity_pos i z).le, smul_eq_mul]
  rw [fsVolumeDensity, mul_comm]

end FSInv

end

end GroundTheory.Heights₂.Heights
