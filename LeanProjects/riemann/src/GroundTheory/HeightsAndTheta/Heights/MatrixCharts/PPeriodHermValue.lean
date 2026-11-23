import Mathlib
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.Statements
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.StatementsCusp
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.TransposeEqOfPosSemidef
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

noncomputable section

namespace PeriodHermValue

theorem re_eq {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (α β : Fin g → ℝ) :
    (fun k => (((fun k => (α k : ℂ)) + τ *ᵥ fun k => (β k : ℂ)) k).re) =
      α + τ.map Complex.re *ᵥ β := by
  ext k
  simp [mulVec, dotProduct, Complex.re_sum, Complex.mul_re]

theorem im_eq {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (α β : Fin g → ℝ) :
    (fun k => (((fun k => (α k : ℂ)) + τ *ᵥ fun k => (β k : ℂ)) k).im) =
      τ.map Complex.im *ᵥ β := by
  ext k
  simp [mulVec, dotProduct, Complex.im_sum, Complex.mul_im]

theorem qf_inv_mulVec {g : ℕ} (Y : Matrix (Fin g) (Fin g) ℝ) (hY : IsUnit Y.det)
    (β : Fin g → ℝ) : MCSchur.qf Y⁻¹ (Y *ᵥ β) = MCSchur.qf Y β := by
  unfold MCSchur.qf
  rw [mulVec_mulVec, nonsing_inv_mul Y hY, one_mulVec, dotProduct_comm]

end PeriodHermValue

theorem PeriodHermValue.proof : PeriodHermValue.Statement := by
  intro g τ hY α β
  rw [MCSchur.hermValue_eq_qf, PeriodHermValue.re_eq, PeriodHermValue.im_eq,
    PeriodHermValue.qf_inv_mulVec _ hY]

end

end GroundTheory.Heights₂.Heights
