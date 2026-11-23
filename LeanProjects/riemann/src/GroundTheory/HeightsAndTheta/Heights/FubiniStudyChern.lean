import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FubiniStudyMetric
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open scoped ContDiff ComplexConjugate Matrix ComplexOrder
open Topology Set

noncomputable section

variable {N : ℕ}

def wirtinger (f : (Fin N → ℂ) → ℂ) (j : Fin N) (z : Fin N → ℂ) : ℂ :=
  (1 / 2 : ℂ) * (fderiv ℝ f z (Pi.single j 1) - Complex.I * fderiv ℝ f z (Pi.single j Complex.I))

def wirtingerBar (f : (Fin N → ℂ) → ℂ) (j : Fin N) (z : Fin N → ℂ) : ℂ :=
  (1 / 2 : ℂ) * (fderiv ℝ f z (Pi.single j 1) + Complex.I * fderiv ℝ f z (Pi.single j Complex.I))

lemma fderiv_coord (k : Fin N) (z : Fin N → ℂ) :
    fderiv ℝ (fun w : Fin N → ℂ => w k) z = ContinuousLinearMap.proj k :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => ℂ) k).fderiv

theorem wirtinger_coord (j k : Fin N) (z : Fin N → ℂ) :
    wirtinger (fun w => w k) j z = if j = k then 1 else 0 := by
  rw [wirtinger, fderiv_coord]
  by_cases h : j = k
  · subst h; simp; norm_num
  · simp [Ne.symm h, h]

theorem wirtingerBar_coord (j k : Fin N) (z : Fin N → ℂ) :
    wirtingerBar (fun w => w k) j z = 0 := by
  rw [wirtingerBar, fderiv_coord]
  by_cases h : j = k
  · subst h; simp
  · simp [Ne.symm h]

def normSqSum (z : Fin N → ℂ) : ℝ := ∑ j, ‖z j‖ ^ 2

lemma normSqSum_nonneg (z : Fin N → ℂ) : 0 ≤ normSqSum z :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma one_add_normSqSum_pos (z : Fin N → ℂ) : 0 < 1 + normSqSum z := by
  have := normSqSum_nonneg z; linarith

def dNormSqSum (z : Fin N → ℂ) : (Fin N → ℂ) →L[ℝ] ℝ :=
  ∑ m, (2 • innerSL ℝ (z m)).comp (ContinuousLinearMap.proj m)

lemma hasFDerivAt_normSqSum (z : Fin N → ℂ) : HasFDerivAt normSqSum (dNormSqSum z) z := by
  have h : ∀ m ∈ (Finset.univ : Finset (Fin N)), HasFDerivAt
      ((fun x : ℂ => ‖x‖ ^ 2) ∘ (fun u : Fin N → ℂ => u m))
      ((2 • innerSL ℝ (z m)).comp (ContinuousLinearMap.proj m)) z := fun m _ =>
    (hasStrictFDerivAt_norm_sq (z m)).hasFDerivAt.comp z (hasFDerivAt_apply (𝕜 := ℝ) m z)
  exact HasFDerivAt.fun_sum h

lemma dNormSqSum_single (z : Fin N → ℂ) (j : Fin N) (w : ℂ) :
    dNormSqSum z (Pi.single j w) = 2 * (w * conj (z j)).re := by
  rw [dNormSqSum, FunLike.coe_sum, Finset.sum_apply, Finset.sum_eq_single j]
  · simp [Complex.inner]; ring
  · intro m _ hm; simp [hm]
  · simp

lemma hasFDerivAt_logPot (z : Fin N → ℂ) :
    HasFDerivAt (fun u => ((Real.log (1 + normSqSum u) : ℝ) : ℂ))
      (Complex.ofRealCLM.comp ((1 + normSqSum z)⁻¹ • dNormSqSum z)) z :=
  Complex.ofRealCLM.hasFDerivAt.comp z
    (((hasFDerivAt_normSqSum z).const_add 1).log (one_add_normSqSum_pos z).ne')

lemma wirtingerBar_logPot (k : Fin N) (z : Fin N → ℂ) :
    wirtingerBar (fun u => ((Real.log (1 + normSqSum u) : ℝ) : ℂ)) k z =
      (((1 + normSqSum z)⁻¹ : ℝ) : ℂ) * z k := by
  rw [wirtingerBar, (hasFDerivAt_logPot z).fderiv]
  simp only [ContinuousLinearMap.comp_apply, FunLike.coe_smul, Pi.smul_apply, dNormSqSum_single,
    Complex.ofRealCLM_apply, smul_eq_mul]
  have h1 : (1 * conj (z k)).re = (z k).re := by simp
  have h2 : (Complex.I * conj (z k)).re = (z k).im := by simp
  rw [h1, h2]
  conv_rhs => rw [← Complex.re_add_im (z k)]
  push_cast
  ring

lemma hasFDerivAt_coordDiv (k : Fin N) (z : Fin N → ℂ) :
    HasFDerivAt (fun u : Fin N → ℂ => (1 + normSqSum u)⁻¹ • u k)
      ((1 + normSqSum z)⁻¹ • (ContinuousLinearMap.proj k : (Fin N → ℂ) →L[ℝ] ℂ) +
        ((-((1 + normSqSum z) ^ 2)⁻¹) • dNormSqSum z).smulRight (z k)) z := by
  have hinv : HasFDerivAt (fun u : Fin N → ℂ => (1 + normSqSum u)⁻¹)
      ((-((1 + normSqSum z) ^ 2)⁻¹) • dNormSqSum z) z :=
    (hasDerivAt_inv (one_add_normSqSum_pos z).ne').comp_hasFDerivAt z
      ((hasFDerivAt_normSqSum z).const_add 1)
  exact hinv.smul (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => ℂ) k).hasFDerivAt

namespace CP

def kahlerPotential (i : Fin (N + 1)) (z : Fin N → ℂ) : ℝ :=
  -Real.log (fsNorm (chartInv i z) (restrictForm (coordForm i) _) ^ 2)

lemma kahlerPotential_eq (i : Fin (N + 1)) (z : Fin N → ℂ) :
    kahlerPotential i z = Real.log (1 + normSqSum z) := by
  rw [kahlerPotential, fsNorm_sq_frame, one_div, Real.log_inv, neg_neg]; rfl

def chernCoeff (i : Fin (N + 1)) (z : Fin N → ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun j k => ((1 / (2 * Real.pi) : ℝ) : ℂ) *
    wirtinger (fun w => wirtingerBar (fun u => ((kahlerPotential i u : ℝ) : ℂ)) k w) j z

theorem chernCoeff_apply (i : Fin (N + 1)) (z : Fin N → ℂ) (j k : Fin N) :
    chernCoeff i z j k = ((1 / (2 * Real.pi * (1 + normSqSum z)) : ℝ) : ℂ) *
      ((1 : Matrix (Fin N) (Fin N) ℂ) j k -
        (((1 + normSqSum z)⁻¹ : ℝ) : ℂ) * (conj (z j) * z k)) := by
  have hpot : (fun u => ((kahlerPotential i u : ℝ) : ℂ)) =
      fun u => ((Real.log (1 + normSqSum u) : ℝ) : ℂ) := by
    funext u; rw [kahlerPotential_eq]
  have hfun : (fun w => wirtingerBar (fun u => ((kahlerPotential i u : ℝ) : ℂ)) k w) =
      fun u : Fin N → ℂ => (1 + normSqSum u)⁻¹ • u k := by
    funext w; rw [hpot, wirtingerBar_logPot, Complex.real_smul]
  rw [chernCoeff, Matrix.of_apply, hfun, wirtinger, (hasFDerivAt_coordDiv k z).fderiv]
  simp only [FunLike.coe_add, Pi.add_apply, FunLike.coe_smul, Pi.smul_apply,
    ContinuousLinearMap.proj_apply, ContinuousLinearMap.smulRight_apply, dNormSqSum_single,
    smul_eq_mul, Complex.real_smul]
  have h1 : (1 * conj (z j)).re = (z j).re := by simp
  have h2 : (Complex.I * conj (z j)).re = (z j).im := by simp
  rw [h1, h2]
  have hS := one_add_normSqSum_pos z
  have hconj : conj (z j) = ((z j).re : ℂ) - ((z j).im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  have hS' : (1 + (normSqSum z : ℂ)) ≠ 0 := by exact_mod_cast hS.ne'
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [hconj, Matrix.one_apply]
  by_cases h : j = k
  · subst h
    simp only [Pi.single_eq_same, if_true]
    push_cast
    field_simp
    ring_nf
    all_goals (try simp only [Complex.I_sq])
    all_goals ring
  · simp only [Pi.single_apply, if_neg (Ne.symm h), if_neg h]
    push_cast
    field_simp
    ring_nf

theorem chernCoeff_eq_matrix (i : Fin (N + 1)) (z : Fin N → ℂ) :
    chernCoeff i z = ((1 / (2 * Real.pi * (1 + normSqSum z)) : ℝ) : ℂ) •
      (1 - (((1 + normSqSum z)⁻¹ : ℝ) : ℂ) • Matrix.vecMulVec (star z) z) := by
  ext j k
  rw [chernCoeff_apply]
  simp [Matrix.vecMulVec_apply]

lemma star_dotProduct_self (x : Fin N → ℂ) : star x ⬝ᵥ x = ((∑ j, ‖x j‖ ^ 2 : ℝ) : ℂ) := by
  simp only [dotProduct, Pi.star_apply, Complex.star_def, Complex.conj_mul']
  push_cast; rfl

theorem chernCoeff_quadForm (i : Fin (N + 1)) (z x : Fin N → ℂ) :
    star x ⬝ᵥ (chernCoeff i z *ᵥ x) = ((1 / (2 * Real.pi * (1 + normSqSum z)) *
      (∑ j, ‖x j‖ ^ 2 - (1 + normSqSum z)⁻¹ * ‖z ⬝ᵥ x‖ ^ 2) : ℝ) : ℂ) := by
  rw [chernCoeff_eq_matrix, Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec,
    Matrix.smul_mulVec, Matrix.vecMulVec_mulVec, op_smul_eq_smul, dotProduct_smul, dotProduct_sub,
    dotProduct_smul, dotProduct_smul, Matrix.star_dotProduct_star, star_dotProduct_self]
  simp only [smul_eq_mul, Complex.star_def, Complex.mul_conj']
  push_cast
  ring

lemma norm_dotProduct_sq_le (z x : Fin N → ℂ) :
    ‖z ⬝ᵥ x‖ ^ 2 ≤ normSqSum z * ∑ j, ‖x j‖ ^ 2 := by
  have h1 : ‖z ⬝ᵥ x‖ ≤ ∑ j, ‖z j‖ * ‖x j‖ := by
    simp only [dotProduct]
    exact (norm_sum_le _ _).trans (le_of_eq (by simp))
  have h2 : (∑ j, ‖z j‖ * ‖x j‖) ^ 2 ≤ (∑ j, ‖z j‖ ^ 2) * (∑ j, ‖x j‖ ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2

theorem chernCoeff_posDef (i : Fin (N + 1)) (z : Fin N → ℂ) : (chernCoeff i z).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · ext j k
    simp only [Matrix.conjTranspose_apply, chernCoeff_apply, Matrix.one_apply]
    by_cases h : j = k
    · subst h; simp [mul_comm]
    · simp [h, Ne.symm h, mul_comm]
  · intro x hx
    rw [chernCoeff_quadForm, Complex.zero_lt_real]
    have hX : 0 < ∑ j, ‖x j‖ ^ 2 := normSq2_pos hx
    have hCS := norm_dotProduct_sq_le z x
    have hS := one_add_normSqSum_pos z
    have hS0 := normSqSum_nonneg z
    refine mul_pos (by positivity) ?_
    rw [sub_pos, inv_mul_lt_iff₀ hS]
    nlinarith

theorem det_chernCoeff (i : Fin (N + 1)) (z : Fin N → ℂ) :
    (chernCoeff i z).det = (((1 / (2 * Real.pi)) ^ N / (1 + normSqSum z) ^ (N + 1) : ℝ) : ℂ) := by
  rw [chernCoeff_eq_matrix, Matrix.det_smul, Fintype.card_fin]
  have hmat : (1 : Matrix (Fin N) (Fin N) ℂ) - (((1 + normSqSum z)⁻¹ : ℝ) : ℂ) •
      Matrix.vecMulVec (star z) z = 1 + Matrix.replicateCol Unit
        (-((((1 + normSqSum z)⁻¹ : ℝ) : ℂ)) • star z) * Matrix.replicateRow Unit z := by
    ext j k
    simp [Matrix.vecMulVec_apply, Matrix.mul_apply, sub_eq_add_neg]
    ring
  have hzz : z ⬝ᵥ star z = ((normSqSum z : ℝ) : ℂ) := by
    rw [dotProduct_comm, star_dotProduct_self]; rfl
  rw [hmat, Matrix.det_one_add_replicateCol_mul_replicateRow, dotProduct_smul, hzz, smul_eq_mul]
  have hS := one_add_normSqSum_pos z
  have hpi := Real.pi_pos
  have key : (1 / (2 * Real.pi * (1 + normSqSum z))) ^ N * (1 + -(1 + normSqSum z)⁻¹ * normSqSum z) =
      (1 / (2 * Real.pi)) ^ N / (1 + normSqSum z) ^ (N + 1) := by
    simp only [div_pow, mul_pow, one_pow, pow_succ]
    field_simp
    ring
  rw [← key]
  push_cast
  ring

def fsVolumeDensity (i : Fin (N + 1)) (z : Fin N → ℂ) : ℝ :=
  (N.factorial : ℝ) * 2 ^ N * ((chernCoeff i z).det).re

theorem fsVolumeDensity_eq (i : Fin (N + 1)) (z : Fin N → ℂ) :
    fsVolumeDensity i z = N.factorial / (Real.pi ^ N * (1 + normSqSum z) ^ (N + 1)) := by
  rw [fsVolumeDensity, det_chernCoeff, Complex.ofReal_re, div_pow, one_pow, mul_pow]
  have hS := one_add_normSqSum_pos z
  have hpi := Real.pi_pos
  field_simp

lemma fsVolumeDensity_pos (i : Fin (N + 1)) (z : Fin N → ℂ) : 0 < fsVolumeDensity i z := by
  rw [fsVolumeDensity_eq]
  have hS := one_add_normSqSum_pos z
  have hpi := Real.pi_pos
  positivity

end CP

end

end GroundTheory.Heights₂.Heights
