import Development.AbelianVarietyTheory.Definitions.Divisors.JoinCastSucc
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinSubstLinSubst

set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice
open Polynomial (nthRootsFinset)
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open MeasureTheory

namespace GlobalTheory.MaxPoint

theorem frameNorm_mulVec {N : ℕ} {A : Matrix (Fin N) (Fin N) ℂ} (hA : A.det ≠ 0) (y : Fin N → ℂ) :
    frameNorm A (A.mulVec y) = Real.sqrt (∑ k, ‖y k‖ ^ 2) := by
  unfold frameNorm
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul A (isUnit_iff_ne_zero.2 hA), Matrix.one_mulVec]

theorem frameNorm_nonneg' {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (x : Fin N → ℂ) : 0 ≤ frameNorm A x :=
  Real.sqrt_nonneg _

theorem frameNorm_smul {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (c : ℂ) (x : Fin N → ℂ) :
    frameNorm A (c • x) = ‖c‖ * frameNorm A x := by
  unfold frameNorm
  rw [Matrix.mulVec_smul]
  simp only [Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow, ← Finset.mul_sum]
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]

theorem eq_zero_of_frameNorm_eq_zero {N : ℕ} {A : Matrix (Fin N) (Fin N) ℂ} (hA : A.det ≠ 0) {x : Fin N → ℂ}
    (h : frameNorm A x = 0) : x = 0 := by
  unfold frameNorm at h
  rw [Real.sqrt_eq_zero (Finset.sum_nonneg fun _ _ => sq_nonneg _)] at h
  have hy : A⁻¹.mulVec x = 0 := by
    funext k
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg ‖A⁻¹.mulVec x i‖)).1 h k (Finset.mem_univ _)
    simpa using this
  calc x = A.mulVec (A⁻¹.mulVec x) := by
        rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.2 hA), Matrix.one_mulVec]
    _ = 0 := by rw [hy, Matrix.mulVec_zero]

theorem eval_linSubst {B N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (h : MvPolynomial (Fin B × Fin N) ℂ)
    (x : Fin B × Fin N → ℂ) :
    eval x (linSubst A h) = eval (fun q => A.mulVec (fun k => x (q.1, k)) q.2) h := by
  unfold linSubst
  rw [eval_aeval_alt]
  simp only [map_sum, map_mul, eval_C, eval_X, Matrix.mulVec, dotProduct]

end GlobalTheory.MaxPoint
