import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.GROWCountStatement

namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

def rmStep (t : ℝ) : ℝ := 2 * Real.smoothTransition (t + 1 / 2) - 1

lemma rmStep_contDiff : ContDiff ℝ ∞ rmStep := by
  unfold rmStep
  exact (contDiff_const.mul (Real.smoothTransition.contDiff.comp (contDiff_id.add contDiff_const))).sub
    contDiff_const

lemma rmStep_continuous : Continuous rmStep := rmStep_contDiff.continuous

lemma rmStep_monotone : Monotone rmStep := by
  intro a b h
  have := Real.smoothTransition.monotone (show a + 1 / 2 ≤ b + 1 / 2 by linarith)
  unfold rmStep
  linarith

lemma rmStep_of_le (t : ℝ) (h : 1 / 2 ≤ t) : rmStep t = 1 := by
  unfold rmStep
  rw [Real.smoothTransition.one_of_one_le (by linarith)]
  norm_num

lemma rmStep_of_ge (t : ℝ) (h : t ≤ -1 / 2) : rmStep t = -1 := by
  unfold rmStep
  rw [Real.smoothTransition.zero_of_nonpos (by linarith)]
  norm_num

lemma abs_rmStep_le (t : ℝ) : |rmStep t| ≤ 1 := by
  have h0 := Real.smoothTransition.nonneg (t + 1 / 2)
  have h1 := Real.smoothTransition.le_one (t + 1 / 2)
  unfold rmStep
  rw [abs_le]
  constructor <;> linarith

def rmPrim (t : ℝ) : ℝ := ∫ s in (0 : ℝ)..t, rmStep s

lemma rmPrim_hasDerivAt (t : ℝ) : HasDerivAt rmPrim (rmStep t) t :=
  (rmStep_continuous.integral_hasStrictDerivAt 0 t).hasDerivAt

def rmRho0 (t : ℝ) : ℝ := (rmPrim t + rmPrim (-t)) / 2

def rmRho (t : ℝ) : ℝ := rmRho0 t + (1 / 2 - rmRho0 (1 / 2))

def rmRho' (t : ℝ) : ℝ := (rmStep t - rmStep (-t)) / 2

lemma rmRho_hasDerivAt (t : ℝ) : HasDerivAt rmRho (rmRho' t) t := by
  have h1 := rmPrim_hasDerivAt t
  have h2 : HasDerivAt (fun s => rmPrim (-s)) (-rmStep (-t)) t := by
    have := (rmPrim_hasDerivAt (-t)).comp t (hasDerivAt_neg t)
    rw [mul_neg_one] at this
    exact this
  have h3 := ((h1.add h2).div_const 2).add_const (1 / 2 - rmRho0 (1 / 2))
  have h4 : rmRho' t = (rmStep t + -rmStep (-t)) / 2 := by
    unfold rmRho'
    ring
  rw [h4]
  exact h3

lemma rmRho_deriv : deriv rmRho = rmRho' := funext fun t => (rmRho_hasDerivAt t).deriv

lemma rmRho'_contDiff : ContDiff ℝ ∞ rmRho' := by
  unfold rmRho'
  exact (rmStep_contDiff.sub (rmStep_contDiff.comp contDiff_neg)).div_const 2

lemma rmRho_contDiff : ContDiff ℝ ∞ rmRho := by
  rw [contDiff_infty_iff_deriv, rmRho_deriv]
  exact ⟨fun t => (rmRho_hasDerivAt t).differentiableAt, rmRho'_contDiff⟩

lemma abs_rmRho'_le (t : ℝ) : |rmRho' t| ≤ 1 := by
  have h1 := abs_le.mp (abs_rmStep_le t)
  have h2 := abs_le.mp (abs_rmStep_le (-t))
  unfold rmRho'
  rw [abs_le]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

lemma rmRho'_monotone : Monotone rmRho' := by
  intro a b h
  have h1 := rmStep_monotone h
  have h2 := rmStep_monotone (show -b ≤ -a by linarith)
  unfold rmRho'
  linarith

lemma rmRho_even (t : ℝ) : rmRho (-t) = rmRho t := by
  unfold rmRho rmRho0
  rw [neg_neg]
  ring

lemma rmRho_of_le (t : ℝ) (h : 1 / 2 ≤ t) : rmRho t = t := by
  have hg : ∀ x ∈ Set.Icc (1 / 2 : ℝ) t, rmRho x - x = rmRho (1 / 2) - 1 / 2 := by
    refine constant_of_has_deriv_right_zero (f := fun x => rmRho x - x) ?_ ?_
    · exact (rmRho_contDiff.continuous.sub continuous_id).continuousOn
    · intro x hx
      have hx1 : 1 / 2 ≤ x := hx.1
      have hd := (rmRho_hasDerivAt x).sub (hasDerivAt_id x)
      have h0 : rmRho' x - 1 = 0 := by
        unfold rmRho'
        rw [rmStep_of_le x hx1, rmStep_of_ge (-x) (by linarith)]
        norm_num
      rw [h0] at hd
      exact hd.hasDerivWithinAt
  have h12 : rmRho (1 / 2) = 1 / 2 := by
    unfold rmRho
    ring
  have := hg t ⟨h, le_rfl⟩
  linarith

lemma rmRho_of_abs (t : ℝ) (h : 1 / 2 ≤ |t|) : rmRho t = |t| := by
  rcases le_or_gt 0 t with h0 | h0
  · rw [abs_of_nonneg h0] at h ⊢
    exact rmRho_of_le t h
  · rw [abs_of_neg h0] at h ⊢
    rw [← rmRho_even]
    exact rmRho_of_le (-t) h

lemma rmRho_lip (a b : ℝ) : |rmRho a - rmRho b| ≤ |a - b| := by
  have hL : LipschitzWith 1 rmRho := by
    refine lipschitzWith_of_nnnorm_deriv_le (fun x => (rmRho_hasDerivAt x).differentiableAt) fun x => ?_
    rw [rmRho_deriv, ← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs, NNReal.coe_one]
    exact abs_rmRho'_le x
  have := hL.dist_le_mul a b
  simpa [Real.dist_eq] using this

lemma rmRho_bounds (t : ℝ) : |t| ≤ rmRho t ∧ rmRho t ≤ |t| + 1 := by
  have h12 : rmRho (1 / 2) = 1 / 2 := by
    unfold rmRho
    ring
  have hanti : Antitone (fun x => rmRho x - x) := by
    have hd : ∀ x, HasDerivAt (fun x => rmRho x - x) (rmRho' x - 1) x :=
      fun x => (rmRho_hasDerivAt x).sub (hasDerivAt_id x)
    refine antitone_of_deriv_nonpos (fun x => (hd x).differentiableAt) fun x => ?_
    rw [(hd x).deriv]
    have := (abs_le.mp (abs_rmRho'_le x)).2
    linarith
  have hge : ∀ s : ℝ, s ≤ rmRho s := by
    intro s
    rcases le_or_gt s (1 / 2) with hs | hs
    · have := hanti hs
      simp only at this
      linarith
    · rw [rmRho_of_le s hs.le]
  constructor
  · rw [abs_le]
    constructor
    · have := hge (-t)
      rw [rmRho_even] at this
      linarith
    · exact hge t
  · have hl := rmRho_lip t (1 / 2)
    have hA : |t - 1 / 2| ≤ |t| + 1 / 2 := abs_le.mpr ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩
    have := le_abs_self (rmRho t - rmRho (1 / 2))
    linarith

variable {n : ℕ}

lemma rm_wdb_ofReal_eventually (F : V n → ℝ) (y : V n) (hF : ContDiffAt ℝ 2 F y) (k : Fin n) :
    wdb n k (fun x => (F x : ℂ)) =ᶠ[𝓝 y] fun x =>
      (((fderiv ℝ F x (bas n k) : ℝ) : ℂ) +
        Complex.I * ((fderiv ℝ F x (Complex.I • bas n k) : ℝ) : ℂ)) / 2 := by
  filter_upwards [hF.eventually (by simp)] with x hx
  have hd : HasFDerivAt (fun x => (F x : ℂ)) (Complex.ofRealCLM.comp (fderiv ℝ F x)) x :=
    Complex.ofRealCLM.hasFDerivAt.comp x (hx.differentiableAt (by norm_num)).hasFDerivAt
  unfold wdb
  rw [hd.fderiv]
  simp

lemma rm_hasFDerivAt_fderiv_apply_ofReal (F : V n → ℝ) (y : V n) (hF : ContDiffAt ℝ 2 F y)
    (w : V n) :
    HasFDerivAt (fun x => ((fderiv ℝ F x w : ℝ) : ℂ))
      (Complex.ofRealCLM.comp ((fderiv ℝ (fderiv ℝ F) y).flip w)) y := by
  have h1 : ContDiffAt ℝ 1 (fderiv ℝ F) y := hF.fderiv_right (by norm_num)
  have h2 : HasFDerivAt (fderiv ℝ F) (fderiv ℝ (fderiv ℝ F) y) y :=
    (h1.differentiableAt (by norm_num)).hasFDerivAt
  have h3 : HasFDerivAt (fun x => fderiv ℝ F x w) ((fderiv ℝ (fderiv ℝ F) y).flip w) y := by
    have := h2.clm_apply (hasFDerivAt_const w y)
    rw [ContinuousLinearMap.comp_zero, zero_add] at this
    exact this
  exact Complex.ofRealCLM.hasFDerivAt.comp y h3

lemma rm_wd_wdb_ofReal (F : V n → ℝ) (y : V n) (hF : ContDiffAt ℝ 2 F y) (j k : Fin n) :
    wd n j (wdb n k (fun x => (F x : ℂ))) y =
      (((fderiv ℝ (fderiv ℝ F) y (bas n j) (bas n k) : ℝ) : ℂ)
        + Complex.I * ((fderiv ℝ (fderiv ℝ F) y (bas n j) (Complex.I • bas n k) : ℝ) : ℂ)
        - Complex.I * ((fderiv ℝ (fderiv ℝ F) y (Complex.I • bas n j) (bas n k) : ℝ) : ℂ)
        + ((fderiv ℝ (fderiv ℝ F) y (Complex.I • bas n j) (Complex.I • bas n k) : ℝ) : ℂ)) / 4 := by
  have hS := (rm_hasFDerivAt_fderiv_apply_ofReal F y hF (bas n k)).add
    ((rm_hasFDerivAt_fderiv_apply_ofReal F y hF (Complex.I • bas n k)).const_mul Complex.I)
  have hG := HasFDerivAt.const_mul (𝔸 := ℂ) hS ((2 : ℂ)⁻¹)
  have hfd := Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) (rm_wdb_ofReal_eventually F y hF k)
  have hfun : (fun x => (((fderiv ℝ F x (bas n k) : ℝ) : ℂ) +
      Complex.I * ((fderiv ℝ F x (Complex.I • bas n k) : ℝ) : ℂ)) / 2) =
      fun x => (2 : ℂ)⁻¹ * (((fun x => ((fderiv ℝ F x (bas n k) : ℝ) : ℂ)) +
        fun y => Complex.I * ((fderiv ℝ F y (Complex.I • bas n k) : ℝ) : ℂ)) x) := by
    funext x
    simp only [Pi.add_apply]
    ring
  unfold wd
  rw [hfd, hfun, hG.fderiv]
  simp
  ring_nf
  rw [Complex.I_sq]
  ring

def rmVec (ξ : Fin n → ℂ) : V n := ∑ j, ξ j • bas n j

lemma rm_cplx_smul_eq (z : ℂ) (x : V n) : z • x = z.re • x + z.im • (Complex.I • x) := by
  conv_lhs => rw [← Complex.re_add_im z]
  rw [add_smul, mul_smul, Complex.coe_smul, Complex.coe_smul]

lemma rm_bil_expand (B : V n →L[ℝ] V n →L[ℝ] ℝ) (z w : ℂ) (a b : V n) :
    B (z • a) (w • b) = z.re * w.re * B a b + z.re * w.im * B a (Complex.I • b)
      + z.im * w.re * B (Complex.I • a) b + z.im * w.im * B (Complex.I • a) (Complex.I • b) := by
  rw [rm_cplx_smul_eq z a, rm_cplx_smul_eq w b]
  simp only [map_add, map_smul, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

lemma rm_bil_sum (B : V n →L[ℝ] V n →L[ℝ] ℝ) (c : Fin n → ℂ) :
    B (∑ j, c j • bas n j) (∑ k, c k • bas n k) = ∑ j, ∑ k, B (c j • bas n j) (c k • bas n k) := by
  simp only [map_sum, ContinuousLinearMap.sum_apply]
  exact Finset.sum_comm

lemma rm_I_smul_vec (ξ : Fin n → ℂ) : Complex.I • rmVec ξ = ∑ j, (Complex.I * ξ j) • bas n j := by
  unfold rmVec
  rw [Finset.smul_sum]
  simp_rw [smul_smul]

theorem rm_levi_re_ofReal (F : V n → ℝ) (y : V n) (hF : ContDiffAt ℝ 2 F y) (ξ : Fin n → ℂ) :
    4 * (leviV n (fun x => (F x : ℂ)) y ξ).re =
      fderiv ℝ (fderiv ℝ F) y (rmVec ξ) (rmVec ξ) +
        fderiv ℝ (fderiv ℝ F) y (Complex.I • rmVec ξ) (Complex.I • rmVec ξ) := by
  rw [rm_I_smul_vec]
  unfold rmVec
  rw [rm_bil_sum, rm_bil_sum, ← Finset.sum_add_distrib]
  unfold leviV
  rw [Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_add_distrib, Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [rm_wd_wdb_ofReal F y hF j k, rm_bil_expand (fderiv ℝ (fderiv ℝ F) y) (ξ j) (ξ k),
    rm_bil_expand (fderiv ℝ (fderiv ℝ F) y) (Complex.I * ξ j) (Complex.I * ξ k)]
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  simp [Complex.mul_re, Complex.mul_im]
  ring

end

end ReciprocityTheory.L2DbarEstimates.Y
