import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsGreenReg
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeLogBound
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PFsLogSmul
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix MeasureTheory
open scoped ContDiff

noncomputable section

namespace FubiniStudyLogRegularization

variable {n : ℕ}

def sqDual (h : HermNorm n) (y : Fin n → ℂ) : ℝ := ∑ i, ‖((h.matᵀ)⁻¹ *ᵥ y) i‖ ^ 2

def regMat (h : HermNorm n) (u : Fin n → ℂ) (ε : ℝ) : Matrix (Fin (n + 1)) (Fin n) ℂ :=
  Matrix.of (Fin.cons u fun i => ((√ε : ℝ) : ℂ) • (h.matᵀ)⁻¹ i)

theorem sqDual_nonneg (h : HermNorm n) (y : Fin n → ℂ) : 0 ≤ sqDual h y :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem dualNorm_sq (h : HermNorm n) (y : Fin n → ℂ) : h.dualNorm y ^ 2 = sqDual h y :=
  Real.sq_sqrt (sqDual_nonneg h y)

theorem sqDual_pos (h : HermNorm n) {y : Fin n → ℂ} (hy : y ≠ 0) : 0 < sqDual h y := by
  rw [← dualNorm_sq]
  exact pow_pos (h.dualNorm_pos hy) 2

theorem fsLogReg_eq (h : HermNorm n) (u : Fin n → ℂ) (ε : ℝ) (y : Fin n → ℂ) :
    fsLogReg h u ε y = Real.log ((‖∑ j, u j * y j‖ ^ 2 + ε * sqDual h y) / sqDual h y) / 2 := by
  rw [fsLogReg, dualNorm_sq]

theorem contDiff_sqDual (h : HermNorm n) : ContDiff ℝ ∞ (sqDual h) := by
  unfold sqDual
  refine ContDiff.sum fun i _ => (contDiff_norm_sq ℝ).comp ?_
  simp only [Matrix.mulVec, dotProduct]
  exact ContDiff.sum fun j _ => contDiff_const.mul (contDiff_apply ℝ ℂ j)

theorem contDiff_lin (u : Fin n → ℂ) : ContDiff ℝ ∞ fun y : Fin n → ℂ => ‖∑ j, u j * y j‖ ^ 2 :=
  (contDiff_norm_sq ℝ).comp (ContDiff.sum fun j _ => contDiff_const.mul (contDiff_apply ℝ ℂ j))

theorem contDiffOn_fsLogReg (h : HermNorm n) (u : Fin n → ℂ) {ε : ℝ} (hε : 0 < ε) :
    ContDiffOn ℝ ∞ (fsLogReg h u ε) {x | x ≠ 0} := by
  intro y hy
  have hS := sqDual_pos h hy
  have hQ : 0 ≤ ‖∑ j, u j * y j‖ ^ 2 := sq_nonneg _
  have hN : 0 < ‖∑ j, u j * y j‖ ^ 2 + ε * sqDual h y := by positivity
  have hD : ContDiffAt ℝ ∞ (fun y => (‖∑ j, u j * y j‖ ^ 2 + ε * sqDual h y) / sqDual h y) y :=
    (((contDiff_lin u).add (contDiff_const.mul (contDiff_sqDual h))).contDiffAt).div
      (contDiff_sqDual h).contDiffAt hS.ne'
  have hf : fsLogReg h u ε = fun y =>
      Real.log ((‖∑ j, u j * y j‖ ^ 2 + ε * sqDual h y) / sqDual h y) / 2 :=
    funext (fsLogReg_eq h u ε)
  rw [hf]
  exact ((hD.log (div_pos hN hS).ne').div_const 2).contDiffWithinAt

theorem fsLogReg_smul (h : HermNorm n) (u : Fin n → ℂ) (ε : ℝ) {t : ℂ} (ht : t ≠ 0)
    (y : Fin n → ℂ) : fsLogReg h u ε (t • y) = fsLogReg h u ε y := by
  have hu : ‖∑ j, u j * (t • y) j‖ = ‖t‖ * ‖∑ j, u j * y j‖ := by
    rw [← norm_mul, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by rw [Pi.smul_apply, smul_eq_mul]; ring
  have ht2 : ‖t‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr ht)
  unfold fsLogReg
  rw [hu, h.dualNorm_smul, mul_pow, mul_pow, ← mul_assoc, mul_comm ε, mul_assoc, ← mul_add,
    mul_div_mul_left _ _ ht2]

theorem fsLogReg_mono (h : HermNorm n) (u : Fin n → ℂ) {δ δ' : ℝ} (hδ : 0 < δ) (hδδ' : δ ≤ δ')
    (y : Fin n → ℂ) : fsLogReg h u δ y ≤ fsLogReg h u δ' y := by
  rw [fsLogReg_eq, fsLogReg_eq]
  rcases (sqDual_nonneg h y).eq_or_lt with hS | hS
  · rw [← hS]
    simp
  have hQ : 0 ≤ ‖∑ j, u j * y j‖ ^ 2 := sq_nonneg _
  have h1 : 0 < (‖∑ j, u j * y j‖ ^ 2 + δ * sqDual h y) / sqDual h y := by positivity
  have h2 : (‖∑ j, u j * y j‖ ^ 2 + δ * sqDual h y) / sqDual h y ≤
      (‖∑ j, u j * y j‖ ^ 2 + δ' * sqDual h y) / sqDual h y :=
    div_le_div_of_nonneg_right (by nlinarith) hS.le
  exact div_le_div_of_nonneg_right (Real.log_le_log h1 h2) zero_le_two

theorem measurable_fsLogReg (h : HermNorm n) (u : Fin n → ℂ) (ε : ℝ) :
    Measurable (fsLogReg h u ε) := by
  have hf : fsLogReg h u ε = fun y =>
      Real.log ((‖∑ j, u j * y j‖ ^ 2 + ε * sqDual h y) / sqDual h y) / 2 :=
    funext (fsLogReg_eq h u ε)
  rw [hf]
  exact ((Real.measurable_log.comp (((contDiff_lin u).continuous.measurable.add
    (measurable_const.mul (contDiff_sqDual h).continuous.measurable)).div
      (contDiff_sqDual h).continuous.measurable)).div_const 2)

theorem sum_regMat (h : HermNorm n) (u : Fin n → ℂ) {ε : ℝ} (hε : 0 ≤ ε) (y : Fin n → ℂ) :
    ∑ i, ‖(regMat h u ε *ᵥ y) i‖ ^ 2 = ‖∑ j, u j * y j‖ ^ 2 + ε * sqDual h y := by
  have h0 : (regMat h u ε *ᵥ y) 0 = ∑ j, u j * y j := by
    simp [regMat, Matrix.mulVec, dotProduct]
  rw [Fin.sum_univ_succ, sqDual, Finset.mul_sum, h0, add_right_inj]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : (regMat h u ε *ᵥ y) i.succ = ((√ε : ℝ) : ℂ) * ((h.matᵀ)⁻¹ *ᵥ y) i := by
    simp only [regMat, Matrix.mulVec, dotProduct, Matrix.of_apply, Fin.cons_succ, Pi.smul_apply,
      smul_eq_mul, Finset.mul_sum, mul_assoc]
  rw [this, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt hε]

theorem regMat_mulVec_ne_zero (h : HermNorm n) (u : Fin n → ℂ) {ε : ℝ} (hε : 0 < ε) {y : Fin n → ℂ}
    (hy : y ≠ 0) : regMat h u ε *ᵥ y ≠ 0 := by
  intro h0
  have hs := sum_regMat h u hε.le y
  rw [h0] at hs
  have hS := sqDual_pos h hy
  have hQ : 0 ≤ ‖∑ j, u j * y j‖ ^ 2 := sq_nonneg _
  simp only [Pi.zero_apply, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    Finset.sum_const_zero] at hs
  nlinarith

theorem log_dualNorm_eq (h : HermNorm n) (y : Fin n → ℂ) :
    Real.log (h.dualNorm y) = Real.log √(∑ i, ‖(regMat h 0 1 *ᵥ y) i‖ ^ 2) := by
  rw [sum_regMat h 0 zero_le_one]
  simp [HermNorm.dualNorm, sqDual]

theorem fsLogReg_add_log (h : HermNorm n) (u : Fin n → ℂ) {ε : ℝ} (hε : 0 < ε) (y : Fin n → ℂ) :
    fsLogReg h u ε y + Real.log (h.dualNorm y) = Real.log √(∑ i, ‖(regMat h u ε *ᵥ y) i‖ ^ 2) := by
  rw [sum_regMat h u hε.le, fsLogReg_eq]
  rcases eq_or_ne y 0 with rfl | hy
  · simp [HermNorm.dualNorm, sqDual]
  have hS := sqDual_pos h hy
  have hQ : 0 ≤ ‖∑ j, u j * y j‖ ^ 2 := sq_nonneg _
  have hN : 0 < ‖∑ j, u j * y j‖ ^ 2 + ε * sqDual h y := by positivity
  rw [Real.log_div hN.ne' hS.ne', Real.log_sqrt hN.le, HermNorm.dualNorm,
    show ∑ i, ‖((h.matᵀ)⁻¹ *ᵥ y) i‖ ^ 2 = sqDual h y from rfl, Real.log_sqrt hS.le]
  ring

end FubiniStudyLogRegularization

end

end GroundTheory.Heights₂.Heights
