import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSectionNormSqLevi
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo Filter Topology ComplexConjugate

noncomputable section

namespace LeviFSInvariant

variable {J : Type} [Fintype J]

def sqSum (z : J → ℂ) : ℝ := ∑ p, ‖z p‖ ^ 2

def reInner (a : J → ℂ) : (J → ℂ) →L[ℝ] ℝ :=
  ∑ p, ((a p).re • (Complex.reCLM.comp (ContinuousLinearMap.proj p)) +
    (a p).im • (Complex.imCLM.comp (ContinuousLinearMap.proj p)))

theorem reInner_apply (a b : J → ℂ) :
    reInner a b = ∑ p, ((a p).re * (b p).re + (a p).im * (b p).im) := by
  simp [reInner]

theorem reInner_comm (a b : J → ℂ) : reInner a b = reInner b a := by
  simp only [reInner_apply]
  exact Finset.sum_congr rfl fun p _ => by ring

theorem reInner_self (a : J → ℂ) : reInner a a = sqSum a := by
  simp only [reInner_apply, sqSum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Complex.sq_norm, Complex.normSq_apply]

theorem continuous_sqSum : Continuous (sqSum : (J → ℂ) → ℝ) := by
  unfold sqSum
  fun_prop

theorem hasFDerivAt_sqSum (z : J → ℂ) : HasFDerivAt sqSum ((2 : ℝ) • reInner z) z := by
  have h := HasFDerivAt.sum (u := Finset.univ) (A := fun p (x : J → ℂ) => ‖x p‖ ^ 2)
    fun p _ => (hasFDerivAt_apply p z).norm_sq
  rw [show (∑ p ∈ Finset.univ, fun x : J → ℂ => ‖x p‖ ^ 2) = sqSum from by
    funext x; simp [sqSum, Finset.sum_apply]] at h
  refine h.congr_fderiv ?_
  refine ContinuousLinearMap.ext fun v => ?_
  simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.coe_smul',
    Pi.smul_apply, ContinuousLinearMap.coe_comp', Function.comp_apply, innerSL_apply_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul, reInner_apply, Complex.inner, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

def phi (z : J → ℂ) : ℝ := Real.log (sqSum z) * (1 / 2)

theorem hasFDerivAt_phi {z : J → ℂ} (hz : sqSum z ≠ 0) :
    HasFDerivAt phi ((sqSum z)⁻¹ • reInner z) z := by
  have h := ((hasFDerivAt_sqSum z).log hz).mul_const (1 / 2 : ℝ)
  refine h.congr_fderiv ?_
  refine ContinuousLinearMap.ext fun v => ?_
  simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul]
  ring

theorem contDiffAt_phi {z : J → ℂ} (hz : sqSum z ≠ 0) {n : WithTop ℕ∞} :
    ContDiffAt ℝ n phi z := by
  have hs : ContDiff ℝ n (sqSum : (J → ℂ) → ℝ) :=
    ContDiff.sum fun p _ => (contDiff_norm_sq ℝ).comp (contDiff_apply ℝ ℂ p)
  exact (hs.contDiffAt.log hz).mul contDiffAt_const

theorem fderiv_fderiv_phi {z : J → ℂ} (hz : sqSum z ≠ 0) (u : J → ℂ) :
    fderiv ℝ (fderiv ℝ phi) z u u =
      sqSum u / sqSum z - 2 * reInner z u ^ 2 / sqSum z ^ 2 := by
  have hd : DifferentiableAt ℝ (fderiv ℝ phi) z :=
    ((contDiffAt_phi hz (n := 2)).fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)
  have h1 : fderiv ℝ (fderiv ℝ phi) z u u = fderiv ℝ (fun z' => fderiv ℝ phi z' u) z u := by
    rw [fderiv_clm_apply hd (differentiableAt_const u)]
    simp
  have hopen : IsOpen {z' : J → ℂ | sqSum z' ≠ 0} := isOpen_ne_fun continuous_sqSum continuous_const
  have heq : (fun z' => fderiv ℝ phi z' u) =ᶠ[𝓝 z]
      fun z' => reInner u z' * ((fun x : ℝ => x⁻¹) ∘ sqSum) z' := by
    filter_upwards [hopen.mem_nhds hz] with z' hz'
    rw [(hasFDerivAt_phi hz').fderiv]
    simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul, Function.comp_apply,
      reInner_comm z' u]
    ring
  have hinv := (hasFDerivAt_inv hz).comp z (hasFDerivAt_sqSum z)
  have hG := (reInner u).hasFDerivAt.mul hinv
  rw [h1, heq.fderiv_eq]
  rw [show (fun z' => reInner u z' * ((fun x : ℝ => x⁻¹) ∘ sqSum) z') =
    (⇑(reInner u) * ((fun x : ℝ => x⁻¹) ∘ sqSum)) from rfl, hG.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
    smul_eq_mul, ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply, reInner_self, reInner_comm u z]
  field_simp
  ring

theorem leviForm_phi {z : J → ℂ} (hz : sqSum z ≠ 0) (w : J → ℂ) :
    leviForm phi z w = (sqSum z * sqSum w - (reInner z w ^ 2 + reInner z (Complex.I • w) ^ 2)) /
      (2 * sqSum z ^ 2) := by
  have hw : sqSum (Complex.I • w) = sqSum w := by
    simp [sqSum]
  unfold leviForm
  rw [fderiv_fderiv_phi hz, fderiv_fderiv_phi hz, hw]
  field_simp
  ring

def herm (a b : J → ℂ) : ℂ := ∑ p, conj (a p) * b p

theorem herm_self (a : J → ℂ) : herm a a = (sqSum a : ℂ) := by
  simp only [herm, sqSum, Complex.ofReal_sum, Complex.ofReal_pow]
  exact Finset.sum_congr rfl fun p _ => Complex.conj_mul' (a p)

theorem herm_swap (a b : J → ℂ) : herm b a = conj (herm a b) := by
  simp only [herm, map_sum, map_mul, Complex.conj_conj]
  exact Finset.sum_congr rfl fun p _ => mul_comm _ _

theorem reInner_sq_add (a b : J → ℂ) :
    ((reInner a b ^ 2 + reInner a (Complex.I • b) ^ 2 : ℝ) : ℂ) = herm a b * herm b a := by
  have hre : (herm a b).re = reInner a b := by
    simp only [herm, Complex.re_sum, reInner_apply, Complex.mul_re, Complex.conj_re, Complex.conj_im]
    exact Finset.sum_congr rfl fun p _ => by ring
  have him : (herm a b).im = -reInner a (Complex.I • b) := by
    simp only [herm, Complex.im_sum, reInner_apply, Complex.mul_im, Complex.conj_re, Complex.conj_im,
      Pi.smul_apply, smul_eq_mul, Complex.mul_re, Complex.I_re, Complex.I_im,
      ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun p _ => by ring
  rw [herm_swap a b, Complex.mul_conj, Complex.normSq_apply, hre, him]
  push_cast
  ring

theorem herm_smul_left (c : ℂ) (a b : J → ℂ) : herm (c • a) b = conj c * herm a b := by
  simp only [herm, Finset.mul_sum, Pi.smul_apply, smul_eq_mul, map_mul]
  exact Finset.sum_congr rfl fun p _ => by ring

theorem herm_add_right (a b b' : J → ℂ) : herm a (b + b') = herm a b + herm a b' := by
  simp only [herm, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem herm_add_left (a a' b : J → ℂ) : herm (a + a') b = herm a b + herm a' b := by
  simp only [herm, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

theorem herm_smul_right (c : ℂ) (a b : J → ℂ) : herm a (c • b) = c * herm a b := by
  simp only [herm, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun p _ => by ring

theorem sqSum_ne_zero {a : J → ℂ} (ha : a ≠ 0) : sqSum a ≠ 0 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp ha
  refine ne_of_gt (lt_of_lt_of_le (pow_pos (norm_pos_iff.mpr hi) 2) ?_)
  exact Finset.single_le_sum (f := fun p => ‖a p‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ i)

end LeviFSInvariant

open LeviFSInvariant in

theorem LeviFSInvariant.proof : LeviFSInvariant.Statement := by
  intro M _ a b c μ ha hc
  have hf : (fun u : M → ℂ => Real.log (∑ j, ‖u j‖ ^ 2) / 2) = phi := by
    funext u
    simp only [phi, sqSum]
    ring
  have hca : c • a ≠ 0 := smul_ne_zero hc ha
  rw [hf, leviForm_phi (sqSum_ne_zero hca), leviForm_phi (sqSum_ne_zero ha)]
  have hS : sqSum (c • a) = ‖c‖ ^ 2 * sqSum a := by
    apply Complex.ofReal_injective
    rw [← herm_self, herm_smul_left, herm_smul_right, herm_self]
    push_cast
    rw [← Complex.conj_mul']
    ring
  have key : ∀ a b : M → ℂ,
      ((sqSum a * sqSum b - (reInner a b ^ 2 + reInner a (Complex.I • b) ^ 2) : ℝ) : ℂ) =
        herm a a * herm b b - herm a b * herm b a := by
    intro a b
    rw [Complex.ofReal_sub, Complex.ofReal_mul, reInner_sq_add, herm_self, herm_self]
  have hN' : herm (c • a) (c • a) * herm (c • b + μ • a) (c • b + μ • a) -
      herm (c • a) (c • b + μ • a) * herm (c • b + μ • a) (c • a) =
      (((‖c‖ ^ 2) ^ 2 : ℝ) : ℂ) * (herm a a * herm b b - herm a b * herm b a) := by
    simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right]
    push_cast
    rw [← Complex.conj_mul']
    ring
  have hN : sqSum (c • a) * sqSum (c • b + μ • a) -
      (reInner (c • a) (c • b + μ • a) ^ 2 + reInner (c • a) (Complex.I • (c • b + μ • a)) ^ 2) =
      (‖c‖ ^ 2) ^ 2 * (sqSum a * sqSum b - (reInner a b ^ 2 + reInner a (Complex.I • b) ^ 2)) := by
    apply Complex.ofReal_injective
    rw [key, Complex.ofReal_mul, key, hN']
  rw [hN, hS]
  have hc2 : ‖c‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hc)
  field_simp

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
