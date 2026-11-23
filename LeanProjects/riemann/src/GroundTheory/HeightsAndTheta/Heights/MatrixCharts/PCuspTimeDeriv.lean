import Mathlib
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.Statements
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.StatementsBounds
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace MCCuspTimeDeriv

theorem lipschitz_norm_coord {n : ℕ} (c : Fin n) :
    LipschitzWith 1 (fun w : Fin n → ℂ => ‖w c‖) := by
  have h := (lipschitzWith_one_norm (E := ℂ)).comp (LipschitzWith.eval (α := fun _ : Fin n => ℂ) c)
  rw [mul_one] at h
  exact h

theorem inv_le_exp_half_log {x : ℝ} (hx : 0 < x) :
    x⁻¹ ≤ Real.exp (Real.log (x ^ 2)⁻¹ / 2) := by
  have h : Real.log (x ^ 2)⁻¹ / 2 = Real.log x⁻¹ := by
    rw [Real.log_inv, Real.log_inv, Real.log_pow]; push_cast; ring
  rw [h, Real.exp_log (inv_pos.mpr hx)]

end MCCuspTimeDeriv

open MCCuspTimeDeriv in

theorem CuspTimeDeriv.proof : CuspTimeDeriv.Statement := by
  intro D z hz i
  set c : Fin D.n := Fin.castLE D.a_le i with hc
  have hz0 : z c ≠ 0 := hz.2 i
  have hlt : ‖z c‖ < 1 := MCBounds.cusp_norm_lt D hz.1 i
  have hpos : 0 < ‖z c‖ := norm_pos_iff.mpr hz0

  let N : (Fin D.n → ℂ) → ℝ := fun w => ‖w c‖
  let φ : ℝ → ℝ := fun y => (2 * Real.pi)⁻¹ * -Real.log y
  have hfun : (fun w => cuspTime D.a_le w i) = φ ∘ N := by
    funext w
    simp only [cuspTime, cuspCoord, φ, N, Function.comp, Real.log_inv, hc]
  have hNd : DifferentiableAt ℝ N z :=
    DifferentiableAt.norm ℂ (differentiableAt_apply (𝕜 := ℝ) c z) hz0
  have hφ : HasDerivAt φ ((2 * Real.pi)⁻¹ * -(‖z c‖)⁻¹) (N z) :=
    ((Real.hasDerivAt_log hpos.ne').neg).const_mul _
  have hcomp : HasFDerivAt (φ ∘ N) (((2 * Real.pi)⁻¹ * -(‖z c‖)⁻¹) • fderiv ℝ N z) z :=
    hφ.comp_hasFDerivAt z hNd.hasFDerivAt
  rw [hfun]
  refine ⟨hcomp.differentiableAt, ?_⟩
  rw [hcomp.fderiv, norm_smul]
  have hNle : ‖fderiv ℝ N z‖ ≤ 1 := by
    have := norm_fderiv_le_of_lipschitz ℝ (x₀ := z) (lipschitz_norm_coord c)
    simpa using this
  have hpi : (2 * Real.pi)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [Real.pi_gt_three])
  have hpi0 : 0 ≤ (2 * Real.pi)⁻¹ := by positivity
  have hcoef : ‖(2 * Real.pi)⁻¹ * -(‖z c‖)⁻¹‖ ≤ (‖z c‖)⁻¹ := by
    rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg hpi0, abs_of_pos (inv_pos.mpr hpos)]
    exact mul_le_of_le_one_left (inv_pos.mpr hpos).le hpi

  have hterm : Real.log (‖z c‖ ^ 2)⁻¹ ≤ D.radius z := by
    have hsum : Real.log (‖cuspCoord D.a_le z i‖ ^ 2)⁻¹ ≤
        ∑ j, Real.log (‖cuspCoord D.a_le z j‖ ^ 2)⁻¹ :=
      Finset.single_le_sum (f := fun j => Real.log (‖cuspCoord D.a_le z j‖ ^ 2)⁻¹)
        (fun j _ => MCBounds.log_inv_sq_nonneg (MCBounds.cusp_norm_lt D hz.1 j)) (Finset.mem_univ i)
    have he := Real.exp_pos 1
    show Real.log (‖cuspCoord D.a_le z i‖ ^ 2)⁻¹ ≤ _
    simp only [PeriodChartData.radius, chartRadius]
    linarith
  have hexp : (‖z c‖)⁻¹ ≤ Real.exp (D.radius z / 2) :=
    (inv_le_exp_half_log hpos).trans (Real.exp_le_exp.mpr (by linarith))
  calc ‖(2 * Real.pi)⁻¹ * -(‖z c‖)⁻¹‖ * ‖fderiv ℝ N z‖ ≤ (‖z c‖)⁻¹ * 1 :=
        mul_le_mul hcoef hNle (norm_nonneg _) (inv_pos.mpr hpos).le
    _ ≤ Real.exp (D.radius z / 2) := by rw [mul_one]; exact hexp

end GroundTheory.Heights₂.Heights
