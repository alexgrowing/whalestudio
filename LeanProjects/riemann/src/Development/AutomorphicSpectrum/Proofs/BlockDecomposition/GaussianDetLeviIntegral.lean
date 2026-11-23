import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JoinCol
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PAreaMultiplicityWeight
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaussianDetSquareIntegralStatement
open MeasureTheory ReciprocityTheory.L2DbarEstimates GlobalTheory.CompanionTheory.FSCrofton
open scoped ENNReal ComplexConjugate

noncomputable section

namespace GlobalTheory.CompanionTheory.FSCrofton.GaussLevi

open Matrix

variable {β : Type} [Fintype β] [DecidableEq β]

def rk (f : β → ℂ) : Matrix β β ℂ := vecMulVec f (star f)

def nS (f : β → ℂ) : ℝ := 1 + ∑ j, ‖f j‖ ^ 2

theorem nS_pos (f : β → ℂ) : 0 < nS f := by
  unfold nS; positivity

theorem star_dot (f : β → ℂ) : star f ⬝ᵥ f = ((nS f - 1 : ℝ) : ℂ) := by
  simp [nS, dotProduct, Complex.conj_mul']

theorem rk_mul_rk (f : β → ℂ) : rk f * rk f = ((nS f - 1 : ℝ) : ℂ) • rk f := by
  unfold rk
  rw [vecMulVec_mul_vecMulVec, star_dot, vecMulVec_smul]

theorem rk_conjTranspose (f : β → ℂ) : (rk f)ᴴ = rk f := by
  unfold rk
  rw [conjTranspose_vecMulVec, star_star]

theorem one_add_mul_one_sub (A : Matrix β β ℂ) (c t u : ℂ) (h : A * A = c • A) :
    (1 + t • A) * (1 - u • A) = 1 + (t - u - t * u * c) • A := by
  simp only [mul_sub, add_mul, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, h, smul_smul]
  module

theorem one_sub_mul_one_sub (A : Matrix β β ℂ) (c u : ℂ) (h : A * A = c • A) :
    (1 - u • A) * (1 - u • A) = 1 + (-(2 * u) + u * u * c) • A := by
  simp only [mul_sub, sub_mul, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, h, smul_smul]
  module

def pM (f : β → ℂ) : Matrix β β ℂ := 1 + ((1 / (1 + √(nS f)) : ℝ) : ℂ) • rk f

def rM (f : β → ℂ) : Matrix β β ℂ := 1 - ((1 / (√(nS f) * (1 + √(nS f))) : ℝ) : ℂ) • rk f

theorem sqrt_facts (f : β → ℂ) : 0 < √(nS f) ∧ √(nS f) * √(nS f) = nS f :=
  ⟨Real.sqrt_pos.2 (nS_pos f), Real.mul_self_sqrt (nS_pos f).le⟩

theorem pM_mul_rM (f : β → ℂ) : pM f * rM f = 1 := by
  obtain ⟨h0, h1⟩ := sqrt_facts f
  unfold pM rM
  rw [one_add_mul_one_sub _ _ _ _ (rk_mul_rk f)]
  have : ((1 / (1 + √(nS f)) : ℝ) : ℂ) - ((1 / (√(nS f) * (1 + √(nS f))) : ℝ) : ℂ) -
      ((1 / (1 + √(nS f)) : ℝ) : ℂ) * ((1 / (√(nS f) * (1 + √(nS f))) : ℝ) : ℂ) *
        ((nS f - 1 : ℝ) : ℂ) = 0 := by
    norm_cast
    generalize √(nS f) = s at h0 h1 ⊢
    rw [← h1]
    field_simp
    ring
  rw [this, zero_smul, add_zero]

theorem rM_conjTranspose (f : β → ℂ) : (rM f)ᴴ = rM f := by
  unfold rM
  rw [conjTranspose_sub, conjTranspose_one, conjTranspose_smul, rk_conjTranspose]
  simp

theorem rM_mul_rM (f : β → ℂ) : rM f * rM f = 1 - ((1 / nS f : ℝ) : ℂ) • rk f := by
  obtain ⟨h0, h1⟩ := sqrt_facts f
  unfold rM
  rw [one_sub_mul_one_sub _ _ _ (rk_mul_rk f), sub_eq_add_neg 1, ← neg_smul]
  congr 2
  norm_cast
  generalize √(nS f) = s at h0 h1 ⊢
  rw [← h1]
  field_simp
  ring

theorem det_pM (f : β → ℂ) : (pM f).det = ((√(nS f) : ℝ) : ℂ) := by
  obtain ⟨h0, h1⟩ := sqrt_facts f
  have e : pM f = 1 + replicateCol Unit (((1 / (1 + √(nS f)) : ℝ) : ℂ) • f) *
      replicateRow Unit (star f) := by
    unfold pM rk
    congr 1
    ext i j
    simp [vecMulVec_apply, Matrix.mul_apply, mul_assoc]
  rw [e, det_one_add_replicateCol_mul_replicateRow, dotProduct_smul, star_dot]
  simp only [smul_eq_mul]
  norm_cast
  generalize √(nS f) = s at h0 h1 ⊢
  rw [← h1]
  field_simp
  ring

theorem vecMul_pM_apply (f r : β → ℂ) (j : β) :
    (r ᵥ* pM f) j = r j + ((1 / (1 + √(nS f)) : ℝ) : ℂ) * (∑ i, r i * f i) * conj (f j) := by
  unfold pM rk
  rw [vecMul_add, vecMul_one, vecMul_smul, vecMul_vecMulVec]
  simp [dotProduct, mul_assoc]

theorem sum_norm_sq_vecMul_pM (f r : β → ℂ) :
    ∑ j, ‖(r ᵥ* pM f) j‖ ^ 2 = ‖∑ i, r i * f i‖ ^ 2 + ∑ j, ‖r j‖ ^ 2 := by
  obtain ⟨h0, h1⟩ := sqrt_facts f
  have ht1 : (1 / (1 + √(nS f))) ^ 2 * (nS f - 1) + 2 * (1 / (1 + √(nS f))) = 1 := by
    generalize √(nS f) = s at h0 h1 ⊢
    rw [← h1]
    field_simp
    ring
  generalize ha : ∑ i, r i * f i = a
  generalize htt : 1 / (1 + √(nS f)) = t at ht1
  have hterm : ∀ j, ‖(r ᵥ* pM f) j‖ ^ 2 =
      ‖r j‖ ^ 2 + t ^ 2 * ‖a‖ ^ 2 * ‖f j‖ ^ 2 + 2 * t * (r j * f j * conj a).re := by
    intro j
    rw [vecMul_pM_apply, ha, htt, Complex.sq_norm, Complex.normSq_add, ← Complex.sq_norm (r j)]
    have e1 : Complex.normSq ((t : ℂ) * a * conj (f j)) = t ^ 2 * ‖a‖ ^ 2 * ‖f j‖ ^ 2 := by
      simp [Complex.normSq_eq_norm_sq, mul_pow]
    have e2 : r j * conj ((t : ℂ) * a * conj (f j)) = (t : ℂ) * (r j * f j * conj a) := by
      simp only [map_mul, Complex.conj_ofReal, Complex.conj_conj]
      ring
    rw [e1, e2, Complex.re_ofReal_mul]
    ring
  have hs : ∑ j, (r j * f j * conj a).re = ‖a‖ ^ 2 := by
    rw [← Complex.re_sum, ← Finset.sum_mul, ha, Complex.mul_conj, Complex.ofReal_re,
      Complex.normSq_eq_norm_sq]
  have hf : ∑ j, ‖f j‖ ^ 2 = nS f - 1 := by simp [nS]
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hs, hf]
  linear_combination ‖a‖ ^ 2 * ht1

theorem lintegral_rows (d : ℕ) (P : Matrix β β ℂ) (hP : P.det ≠ 0)
    (H : (Fin d → β → ℂ) → ℝ≥0∞) (hH : Measurable H) :
    ∫⁻ C : Fin d → β → ℂ, H (fun k => C k ᵥ* P) =
      ENNReal.ofReal |((Complex.normSq P.det) ^ d)⁻¹| * ∫⁻ D, H D := by
  let T : (β → ℂ) →ₗ[ℝ] (β → ℂ) := (Matrix.toLin' Pᵀ).restrictScalars ℝ
  let L : (Fin d → β → ℂ) →ₗ[ℝ] (Fin d → β → ℂ) := LinearMap.pi fun k => T ∘ₗ LinearMap.proj k
  have hdT : LinearMap.det T = Complex.normSq P.det := by
    simp only [T]
    rw [LinearMap.det_restrictScalars, LinearMap.det_toLin', Matrix.det_transpose,
      Algebra.norm_complex_apply]
  have hdL : LinearMap.det L = (Complex.normSq P.det) ^ d := by
    simp only [L]
    rw [LinearMap.det_pi, Finset.prod_const, hdT]
    simp
  have hne : LinearMap.det L ≠ 0 := by
    rw [hdL]
    exact pow_ne_zero _ (Complex.normSq_pos.2 hP).ne'
  have hL : (fun C : Fin d → β → ℂ => fun k => C k ᵥ* P) = L := by
    funext C k
    simp [L, T, toLin'_apply, mulVec_transpose]
  have hLm : Measurable L := L.continuous_of_finiteDimensional.measurable
  haveI : (volume : Measure (β → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI : (volume : Measure (Fin d → β → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have e : ∫⁻ C : Fin d → β → ℂ, H (fun k => C k ᵥ* P) = ∫⁻ C, H (L C) := by
    rw [← hL]
  rw [e, ← lintegral_map hH hLm, Measure.map_linearMap_addHaar_eq_smul_addHaar _ hne,
    lintegral_smul_measure, hdL]
  rfl

theorem gram_eq {d : ℕ} (f : β → ℂ) (F : Matrix β (Fin d) ℂ) :
    (rM f * F)ᴴ * (rM f * F) =
      Fᴴ * F - ((1 / nS f : ℝ) : ℂ) • vecMulVec (Fᴴ *ᵥ f) (star f ᵥ* F) := by
  rw [conjTranspose_mul, rM_conjTranspose, Matrix.mul_assoc, ← Matrix.mul_assoc (rM f), rM_mul_rM,
    Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul]
  congr 2
  unfold rk
  rw [vecMulVec_mul, mul_vecMulVec]

theorem fsLevi_eq {d : ℕ} (f : β → ℂ) (F : Matrix β (Fin d) ℂ) :
    fsLevi f F = ((1 / nS f : ℝ) : ℂ) • ((rM f * F)ᴴ * (rM f * F))ᵀ := by
  have hS : ((nS f : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (nS_pos f).ne'
  rw [gram_eq]
  ext a c
  have hX : ∑ j, F j a * conj (F j c) = (Fᴴ * F) c a := by
    simp [Matrix.mul_apply, mul_comm]
  have hY : ∑ j, F j a * conj (f j) = (star f ᵥ* F) a := by
    simp [vecMul, dotProduct, mul_comm]
  have hZ : ∑ j, f j * conj (F j c) = (Fᴴ *ᵥ f) c := by
    simp [mulVec, dotProduct, mul_comm]
  have h1 : ((1 + ∑ j, ‖f j‖ ^ 2 : ℝ) : ℂ) = ((nS f : ℝ) : ℂ) := rfl
  simp only [fsLevi, of_apply, hX, hY, hZ, h1, Matrix.smul_apply, transpose_apply, Matrix.sub_apply,
    vecMulVec_apply, smul_eq_mul]
  push_cast
  field_simp

theorem lintegral_gauss_levi : ∀ (d : ℕ) (β : Type) [Fintype β] [DecidableEq β] (f : β → ℂ)
    (F : Matrix β (Fin d) ℂ),
    ∫⁻ C : Fin d → β → ℂ, gW d β C *
        ENNReal.ofReal (Real.exp (-∑ k, ‖∑ j, C k j * f j‖ ^ 2) * ‖(Matrix.of C * F).det‖ ^ 2) =
      ENNReal.ofReal (Real.pi ^ (d * Fintype.card β) * (d.factorial : ℝ) * (fsLevi f F).det.re) := by
  intro d β _ _ f F
  obtain ⟨h0, h1⟩ := sqrt_facts f
  have hSp := nS_pos f
  let G : Matrix β (Fin d) ℂ := rM f * F
  let H : (Fin d → β → ℂ) → ℝ≥0∞ := fun D =>
    gW d β D * ENNReal.ofReal (‖(Matrix.of D * G).det‖ ^ 2)
  have hH : Measurable H := by
    have c1 : Continuous fun D : Fin d → β → ℂ => Real.exp (-∑ k, ∑ j, ‖D k j‖ ^ 2) := by
      fun_prop
    have c2 : Continuous fun D : Fin d → β → ℂ => (Matrix.of D * G).det :=
      Continuous.matrix_det (Continuous.matrix_mul continuous_id continuous_const)
    exact (ENNReal.measurable_ofReal.comp c1.measurable).mul
      (ENNReal.measurable_ofReal.comp (c2.norm.pow 2).measurable)
  have hpt : ∀ C : Fin d → β → ℂ, gW d β C *
      ENNReal.ofReal (Real.exp (-∑ k, ‖∑ j, C k j * f j‖ ^ 2) * ‖(Matrix.of C * F).det‖ ^ 2) =
      H (fun k => C k ᵥ* pM f) := by
    intro C
    have hrow : Matrix.of (fun k => C k ᵥ* pM f) = Matrix.of C * pM f := by
      ext k j
      simp [vecMul, Matrix.mul_apply, dotProduct]
    have hdet : Matrix.of (fun k => C k ᵥ* pM f) * G = Matrix.of C * F := by
      rw [hrow, Matrix.mul_assoc]
      simp only [G]
      rw [← Matrix.mul_assoc (pM f), pM_mul_rM, Matrix.one_mul]
    simp only [H, gW]
    rw [hdet]
    simp_rw [sum_norm_sq_vecMul_pM]
    rw [ENNReal.ofReal_mul (Real.exp_pos _).le, ← mul_assoc,
      ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, Finset.sum_add_distrib]
    congr 3
    ring
  have hPd : (pM f).det ≠ 0 := by
    rw [det_pM]
    exact_mod_cast h0.ne'
  simp_rw [hpt]
  rw [lintegral_rows d (pM f) hPd H hH]
  have hI : ∫⁻ D, H D = ENNReal.ofReal (Real.pi ^ (d * Fintype.card β) * (d.factorial : ℝ) *
      (G.conjTranspose * G).det.re) := GlobalTheory.T.gaussian_det_square_integral d β G
  rw [hI, ← ENNReal.ofReal_mul (abs_nonneg _)]
  congr 1
  have hn : Complex.normSq (pM f).det = nS f := by
    rw [det_pM, Complex.normSq_ofReal, h1]
  have hL : (fsLevi f F).det.re = (1 / nS f) ^ d * (G.conjTranspose * G).det.re := by
    rw [fsLevi_eq, Matrix.det_smul, Matrix.det_transpose, Fintype.card_fin]
    simp only [G]
    rw [← Complex.ofReal_pow, Complex.re_ofReal_mul]
  rw [hn, hL, abs_of_pos (inv_pos.2 (pow_pos hSp d)), one_div, inv_pow]
  ring

end GlobalTheory.CompanionTheory.FSCrofton.GaussLevi
