import Mathlib
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.Statements
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.StatementsPsh
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PshMean
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

noncomputable section

theorem cuspTime_continuousOn {n a : ℕ} (h : a ≤ n) (U : Set (Fin n → ℂ)) (j : Fin a) :
    ContinuousOn (fun z => cuspTime h z j) (puncturedChart h U) := by
  have hc : Continuous (fun z : Fin n → ℂ => cuspCoord h z j) := continuous_apply _
  have hne : ∀ z ∈ puncturedChart h U, ‖cuspCoord h z j‖ ≠ 0 := fun z hz =>
    norm_ne_zero_iff.mpr (hz.2 j)
  have hinv : ContinuousOn (fun z => ‖cuspCoord h z j‖⁻¹) (puncturedChart h U) :=
    hc.norm.continuousOn.inv₀ hne
  exact continuousOn_const.mul (hinv.log fun z hz => inv_ne_zero (hne z hz))

theorem ChartImagContinuous.proof : ChartImagContinuous.Statement := by
  intro D
  have hsub : D.Ustar ⊆ D.U := fun z hz => hz.1
  have hτ : ∀ k l, ContinuousOn (fun z => (D.τ0 z k l).im) D.Ustar := fun k l =>
    Complex.continuous_im.comp_continuousOn ((D.τ0_analytic k l).continuousOn.mono hsub)
  have ht : ∀ j, ContinuousOn (fun z => cuspTime D.a_le z j) D.Ustar := fun j =>
    cuspTime_continuousOn D.a_le D.U j
  show ContinuousOn (fun z => chartImag D.a_le D.τ0 D.B z) D.Ustar
  refine continuousOn_pi.mpr fun k => continuousOn_pi.mpr fun l => ?_
  simp only [chartImag, Matrix.add_apply, Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul]
  exact (hτ k l).add (continuousOn_finsetSum _ fun j _ => (ht j).mul continuousOn_const)

end

end GroundTheory.Heights₂.Heights
