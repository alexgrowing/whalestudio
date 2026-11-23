import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree.FubiniLevi

open ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

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

theorem sqSum_nonneg (z : J → ℂ) : 0 ≤ sqSum z :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

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

section Line

theorem sum_line (f : (Σ _ : Unit, Fin 2) → ℝ) : ∑ p, f p = f ⟨(), 0⟩ + f ⟨(), 1⟩ := by
  rw [Fintype.sum_sigma]
  simp [Fin.sum_univ_two]

theorem lagrange (z w : (Σ _ : Unit, Fin 2) → ℂ) :
    sqSum z * sqSum w - (reInner z w ^ 2 + reInner z (Complex.I • w) ^ 2) =
      Complex.normSq (z ⟨(), 0⟩ * w ⟨(), 1⟩ - z ⟨(), 1⟩ * w ⟨(), 0⟩) := by
  simp only [sqSum, reInner_apply, sum_line, Complex.sq_norm, Complex.normSq_apply, Pi.smul_apply,
    smul_eq_mul, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.sub_re,
    Complex.sub_im]
  ring

theorem levi_phi_pos {z w : (Σ _ : Unit, Fin 2) → ℂ} (hz : ∃ i, z ⟨(), i⟩ ≠ 0)
    (hw : ∀ c : ℂ, w ≠ fun p => c * z p) : 0 < leviForm phi z w := by
  have hS : sqSum z ≠ 0 := by
    obtain ⟨i, hi⟩ := hz
    refine ne_of_gt (lt_of_lt_of_le (pow_pos (norm_pos_iff.mpr hi) 2) ?_)
    exact Finset.single_le_sum (f := fun p => ‖z p‖ ^ 2) (fun _ _ => sq_nonneg _)
      (Finset.mem_univ (⟨(), i⟩ : Σ _ : Unit, Fin 2))
  rw [leviForm_phi hS, lagrange]
  refine div_pos (Complex.normSq_pos.mpr fun h0 => ?_) (by positivity)
  rw [sub_eq_zero] at h0
  have hcases : ∀ p : Σ _ : Unit, Fin 2, p = ⟨(), 0⟩ ∨ p = ⟨(), 1⟩ := by
    rintro ⟨⟨⟩, j⟩
    fin_cases j <;> simp
  by_cases hz0 : z ⟨(), 0⟩ = 0
  · have hz1 : z ⟨(), 1⟩ ≠ 0 := fun h1 => hS (by simp [sqSum, sum_line, hz0, h1])
    apply hw (w ⟨(), 1⟩ / z ⟨(), 1⟩)
    funext p
    rcases hcases p with rfl | rfl
    · rw [hz0, zero_mul] at h0
      have hw0 : w ⟨(), 0⟩ = 0 := by
        rcases mul_eq_zero.mp h0.symm with h | h
        · exact absurd h hz1
        · exact h
      rw [hw0, hz0, mul_zero]
    · rw [div_mul_cancel₀ _ hz1]
  · apply hw (w ⟨(), 0⟩ / z ⟨(), 0⟩)
    funext p
    rcases hcases p with rfl | rfl
    · rw [div_mul_cancel₀ _ hz0]
    · rw [div_mul_eq_mul_div, eq_div_iff hz0]
      linear_combination h0

theorem log_fsLine (z : (Σ _ : Unit, Fin 2) → ℂ) : Real.log ((fsLine 2).h z) = phi z := by
  have hfun : (fsLine 2).h z = ∏ k : Unit, Real.sqrt (∑ i : Fin 2, ‖z ⟨k, i⟩‖ ^ 2) := by
    simp only [fsLine, HermLine.ofMetrics, fsMetric, Pi.one_apply, zpow_one, EuclideanSpace.norm_eq]
  rw [hfun, Fintype.prod_unique, Real.log_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _), phi,
    sqSum, sum_line]
  simp [Fin.sum_univ_two]
  ring

end Line

end GroundTheory.Heights₂.Heights.LowerBoundFree.FubiniLevi
