import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsGreenReg
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeLogBound
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PFsLogSmul
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

variable {n : ℕ}

def SliceCutOffLimit.Statement : Prop :=
  ∀ (n e : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
    (g : MvPolynomial (Fin (e + 2) × Fin n) ℂ) (ℓ : Fin n → ℂ),
    IsProjPrime W → IsChowForm W (e + 2) g → linForm ℓ ∉ W →
      ∃ χ : ℕ → (Fin n → ℂ) → ℝ, (∀ k, ContDiff ℝ ∞ (χ k)) ∧ (∀ k, HasCompactSupport (χ k)) ∧
        ∀ F G : (Fin n → ℂ) → ℝ,
          (∀ (t : ℂ) (x : Fin n → ℂ), t ≠ 0 → F (t • x) = F x) →
          (∀ (t : ℂ) (x : Fin n → ℂ), t ≠ 0 → G (t • x) = G x) →
          ContDiffOn ℝ ∞ F {x | x ≠ 0} → ContDiffOn ℝ ∞ G {x | x ≠ 0} →
            Tendsto (fun k =>
                varInt (W ⊔ Ideal.span {linForm ℓ - 1}) (e + 1) (fun x => χ k x * F x)
                  (vecCons G fun _ x => Real.log (h.dualNorm x))) atTop
              (𝓝 (varInt (W ⊔ Ideal.span {linForm ℓ - 1}) (e + 1) F
                (vecCons G fun _ x => Real.log (h.dualNorm x)))) ∧
            Tendsto (fun k =>
                varInt (W ⊔ Ideal.span {linForm ℓ - 1}) (e + 1) G
                  (vecCons (fun x => χ k x * F x) fun _ x => Real.log (h.dualNorm x))) atTop
              (𝓝 (varInt (W ⊔ Ideal.span {linForm ℓ - 1}) (e + 1) G
                (vecCons F fun _ x => Real.log (h.dualNorm x))))

theorem HermNorm.dualNorm_sq (h : HermNorm n) (y : Fin n → ℂ) :
    h.dualNorm y ^ 2 = ∑ i, ‖((h.matᵀ)⁻¹ *ᵥ y) i‖ ^ 2 :=
  Real.sq_sqrt (by positivity)

theorem HermNorm.contDiff_dualNorm_sq (h : HermNorm n) :
    ContDiff ℝ ∞ fun y : Fin n → ℂ => h.dualNorm y ^ 2 := by
  simp_rw [HermNorm.dualNorm_sq]
  refine ContDiff.sum fun i _ => (contDiff_norm_sq ℝ).comp ?_
  simp only [Matrix.mulVec, dotProduct]
  exact ContDiff.sum fun j _ => contDiff_const.mul (contDiff_apply ℝ ℂ j)

theorem HermNorm.contDiffOn_log_dualNorm (h : HermNorm n) :
    ContDiffOn ℝ ∞ (fun y : Fin n → ℂ => Real.log (h.dualNorm y)) {y | y ≠ 0} := by
  have he : (fun y : Fin n → ℂ => Real.log (h.dualNorm y)) =
      fun y => Real.log (h.dualNorm y ^ 2) / 2 := by
    funext y
    rw [Real.log_pow]
    push_cast
    ring
  rw [he]
  exact (h.contDiff_dualNorm_sq.contDiffOn.log fun y hy =>
    (pow_pos (h.dualNorm_pos hy) 2).ne').div_const 2

theorem fsLogReg_smul (h : HermNorm n) (u : Fin n → ℂ) (ε : ℝ) (t : ℂ) (x : Fin n → ℂ)
    (ht : t ≠ 0) : fsLogReg h u ε (t • x) = fsLogReg h u ε x := by
  have hs : ∑ j, u j * (t • x) j = t * ∑ j, u j * x j := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by simp only [Pi.smul_apply, smul_eq_mul]; ring
  have ht2 : ‖t‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr ht)
  unfold fsLogReg
  rw [hs, h.dualNorm_smul, norm_mul, mul_pow, mul_pow, mul_left_comm ε, ← mul_add,
    mul_div_mul_left _ _ ht2]

theorem contDiffOn_fsLogReg (h : HermNorm n) (u : Fin n → ℂ) {ε : ℝ} (hε : 0 < ε) :
    ContDiffOn ℝ ∞ (fsLogReg h u ε) {y | y ≠ 0} := by
  have hnum : ContDiff ℝ ∞ fun y : Fin n → ℂ => ‖∑ j, u j * y j‖ ^ 2 + ε * h.dualNorm y ^ 2 :=
    ((contDiff_norm_sq ℝ).comp (ContDiff.sum fun j _ => contDiff_const.mul (contDiff_apply ℝ ℂ j))).add
      (contDiff_const.mul h.contDiff_dualNorm_sq)
  have hpos : ∀ y : Fin n → ℂ, y ≠ 0 → 0 < h.dualNorm y ^ 2 := fun y hy =>
    pow_pos (h.dualNorm_pos hy) 2
  refine ((hnum.contDiffOn.div h.contDiff_dualNorm_sq.contDiffOn fun y hy => (hpos y hy).ne').log
    fun y hy => ?_).div_const 2
  have := hpos y hy
  exact (div_pos (by positivity) this).ne'

end

end GroundTheory.Heights₂.Heights
