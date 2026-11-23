import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.HoloWeakStatement

namespace ReciprocityTheory.L2DbarEstimates.C

open MeasureTheory Metric Set Filter Topology Complex
open scoped ENNReal

noncomputable section

def cutL (ε s : ℝ) : ℝ := Real.log (s + ε) - Real.log ε

def cutP (ε s : ℝ) : ℝ := cutL ε s ^ 2 / 2

def halfLogRatioSqDeriv (ε s : ℝ) : ℝ := cutL ε s / (s + ε)

def halfLogRatioSqSecondDeriv (ε s : ℝ) : ℝ := (1 - cutL ε s) / (s + ε) ^ 2

lemma hasDerivAt_cutL {ε s : ℝ} (h : 0 < s + ε) : HasDerivAt (cutL ε) (s + ε)⁻¹ s := by
  have h1 := (((hasDerivAt_id s).add_const ε).log h.ne').sub_const (Real.log ε)
  show HasDerivAt (fun s => Real.log (s + ε) - Real.log ε) _ s
  simpa [one_div] using h1

lemma hasDerivAt_cutP {ε s : ℝ} (h : 0 < s + ε) : HasDerivAt (cutP ε) (halfLogRatioSqDeriv ε s) s := by
  have h1 := ((hasDerivAt_cutL h).pow 2).div_const 2
  show HasDerivAt (fun s => cutL ε s ^ 2 / 2) _ s
  refine h1.congr_deriv ?_
  unfold halfLogRatioSqDeriv
  field_simp
  ring

lemma hasDerivAt_halfLogRatioSqDeriv {ε s : ℝ} (h : 0 < s + ε) : HasDerivAt (halfLogRatioSqDeriv ε) (halfLogRatioSqSecondDeriv ε s) s := by
  have h1 := (hasDerivAt_cutL h).div ((hasDerivAt_id s).add_const ε) h.ne'
  show HasDerivAt (fun s => cutL ε s / (s + ε)) _ s
  refine h1.congr_deriv ?_
  unfold halfLogRatioSqSecondDeriv
  simp only [id]
  field_simp

lemma cutL_nonneg {ε s : ℝ} (hε : 0 < ε) (hs : 0 ≤ s) : 0 ≤ cutL ε s := by
  unfold cutL
  exact sub_nonneg.2 (Real.log_le_log hε (by linarith))

lemma cutL_mono {ε s t : ℝ} (hε : 0 < ε) (hs : 0 ≤ s) (hst : s ≤ t) : cutL ε s ≤ cutL ε t := by
  unfold cutL
  exact sub_le_sub_right (Real.log_le_log (by linarith) (by linarith)) _

lemma polydiscCutoff_nonneg (ε s : ℝ) : 0 ≤ cutP ε s := by
  unfold cutP
  positivity

lemma cutP_mono {ε s t : ℝ} (hε : 0 < ε) (hs : 0 ≤ s) (hst : s ≤ t) : cutP ε s ≤ cutP ε t := by
  unfold cutP
  nlinarith [cutL_nonneg hε hs, cutL_mono hε hs hst]

lemma cut_rho_eq {ε s : ℝ} (h : 0 < s + ε) :
    s * halfLogRatioSqSecondDeriv ε s + halfLogRatioSqDeriv ε s = (s + ε * cutL ε s) / (s + ε) ^ 2 := by
  unfold halfLogRatioSqSecondDeriv halfLogRatioSqDeriv
  field_simp
  ring

lemma cut_rho_nonneg {ε s : ℝ} (hε : 0 < ε) (hs : 0 ≤ s) : 0 ≤ s * halfLogRatioSqSecondDeriv ε s + halfLogRatioSqDeriv ε s := by
  rw [cut_rho_eq (by linarith)]
  exact div_nonneg (add_nonneg hs (mul_nonneg hε.le (cutL_nonneg hε hs))) (by positivity)

lemma cut_rho_ge {ε s : ℝ} (hε : 0 < ε) (hs : ε ≤ s) :
    s⁻¹ ≤ 4 * (s * halfLogRatioSqSecondDeriv ε s + halfLogRatioSqDeriv ε s) := by
  have hs0 : 0 < s := lt_of_lt_of_le hε hs
  have hL := cutL_nonneg hε hs0.le
  rw [cut_rho_eq (by linarith), inv_eq_one_div, mul_div_assoc', div_le_div_iff₀ hs0 (by positivity)]
  nlinarith [mul_nonneg (sub_nonneg.2 hs) (by linarith : (0 : ℝ) ≤ 3 * s + ε),
    mul_nonneg hs0.le (mul_nonneg hε.le hL)]

lemma cutP_le {k m : ℝ} (hk : 1 ≤ k) (hm : 0 ≤ m) :
    cutP (Real.exp (-2 * k)) m ≤ (m + 2) ^ 2 / 2 * k ^ 2 := by
  have hε : 0 < Real.exp (-2 * k) := Real.exp_pos _
  have hε1 : Real.exp (-2 * k) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hLe : cutL (Real.exp (-2 * k)) m = Real.log (m + Real.exp (-2 * k)) + 2 * k := by
    unfold cutL
    rw [Real.log_exp]
    ring
  have hlog : Real.log (m + Real.exp (-2 * k)) ≤ m + Real.exp (-2 * k) - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  have hL0 := cutL_nonneg hε hm
  have hLup : cutL (Real.exp (-2 * k)) m ≤ (m + 2) * k := by
    rw [hLe]
    nlinarith
  unfold cutP
  nlinarith [mul_le_mul hLup hLup hL0 (by positivity : (0 : ℝ) ≤ (m + 2) * k)]

lemma continuousAt_cutP {ε s : ℝ} (h : 0 < s + ε) : ContinuousAt (cutP ε) s :=
  (hasDerivAt_cutP h).continuousAt

lemma continuousAt_halfLogRatioSqDeriv {ε s : ℝ} (h : 0 < s + ε) : ContinuousAt (halfLogRatioSqDeriv ε) s :=
  (hasDerivAt_halfLogRatioSqDeriv h).continuousAt

lemma continuousAt_halfLogRatioSqSecondDeriv {ε s : ℝ} (h : 0 < s + ε) : ContinuousAt (halfLogRatioSqSecondDeriv ε) s := by
  show ContinuousAt (fun s => (1 - cutL ε s) / (s + ε) ^ 2) s
  exact (continuousAt_const.sub (hasDerivAt_cutL h).continuousAt).div (by fun_prop)
    (pow_ne_zero 2 h.ne')

variable {n : ℕ}

def complexLineSecondDeriv (F : V n → ℂ) (z e : V n) : ℂ := deriv (deriv (fun l : ℂ => F (z + l • e))) 0

lemma real_smul_smul (t : ℝ) (μ : ℂ) (e : V n) : t • (μ • e) = ((t : ℂ) * μ) • e := by
  rw [← Complex.coe_smul, smul_smul]

lemma deriv_slice {Ω : Set (V n)} {F : V n → ℂ} (hΩ : IsOpen Ω) (hF : DifferentiableOn ℂ F Ω)
    {z e : V n} {l : ℂ} (hw : z + l • e ∈ Ω) :
    deriv (fun m : ℂ => F (z + m • e)) l = fderiv ℂ F (z + l • e) e := by
  have hd : DifferentiableAt ℂ F (z + l • e) := hF.differentiableAt (hΩ.mem_nhds hw)
  have hl : HasDerivAt (fun m : ℂ => z + m • e) e l := by
    simpa using ((hasDerivAt_id l).smul_const e).const_add z
  exact (hd.hasFDerivAt.comp_hasDerivAt l hl).deriv

lemma hasDerivAt_line {Ω : Set (V n)} {F : V n → ℂ} (hΩ : IsOpen Ω) (hF : DifferentiableOn ℂ F Ω)
    {z : V n} (hz : z ∈ Ω) (e : V n) (μ : ℂ) :
    HasDerivAt (fun t : ℝ => F (z + t • (μ • e))) (fderiv ℂ F z e * μ) 0 := by
  have hd : DifferentiableAt ℂ F z := hF.differentiableAt (hΩ.mem_nhds hz)
  have hl : HasDerivAt (fun t : ℝ => z + t • (μ • e)) ((1 : ℝ) • (μ • e)) 0 :=
    ((hasDerivAt_id (0 : ℝ)).smul_const (μ • e)).const_add z
  have h1 := (hd.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)
  refine h1.congr_deriv ?_
  rw [one_smul, ContinuousLinearMap.coe_restrictScalars', map_smul, smul_eq_mul, mul_comm]

lemma hasDerivAt_realLine_fderiv {Ω : Set (V n)} {F : V n → ℂ} (hΩ : IsOpen Ω)
    (hF : DifferentiableOn ℂ F Ω) {z : V n} (hz : z ∈ Ω) (e : V n) (μ : ℂ) :
    HasDerivAt (fun t : ℝ => fderiv ℂ F (z + t • (μ • e)) e) (complexLineSecondDeriv F z e * μ) 0 := by
  have hU : IsOpen {l : ℂ | z + l • e ∈ Ω} := hΩ.preimage (by fun_prop)
  have h0 : (0 : ℂ) ∈ {l : ℂ | z + l • e ∈ Ω} := by simpa using hz
  have hg : DifferentiableOn ℂ (fun l : ℂ => F (z + l • e)) {l : ℂ | z + l • e ∈ Ω} :=
    hF.comp (by fun_prop) (fun l hl => hl)
  have hg' := hg.deriv hU

  have hder : HasDerivAt (deriv fun l : ℂ => F (z + l • e)) (complexLineSecondDeriv F z e) (((0 : ℝ) : ℂ) * μ) := by
    have h1 := ((hg' 0 h0).differentiableAt (hU.mem_nhds h0)).hasDerivAt
    simpa [complexLineSecondDeriv] using h1
  have hc : HasDerivAt (fun t : ℝ => (t : ℂ) * μ) μ 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).ofReal_comp).mul_const μ
  have hcomp := hder.comp (0 : ℝ) hc
  refine hcomp.congr_of_eventuallyEq ?_
  have h0' : ((0 : ℝ) : ℂ) * μ ∈ {l : ℂ | z + l • e ∈ Ω} := by simpa using hz
  filter_upwards [hc.continuousAt.preimage_mem_nhds (hU.mem_nhds h0')] with t ht
  show fderiv ℂ F (z + t • (μ • e)) e = deriv (fun l : ℂ => F (z + l • e)) ((t : ℂ) * μ)
  rw [real_smul_smul]
  exact (deriv_slice hΩ hF ht).symm

lemma cauchy_deriv_le {g : ℂ → ℂ} {c : ℂ} {R M : ℝ} (hR : 0 < R)
    (hg : DifferentiableOn ℂ g (closedBall c R)) (hM : ∀ w ∈ closedBall c R, ‖g w‖ ≤ M) :
    ‖deriv g c‖ ≤ M / R := by
  have hd : DiffContOnCl ℂ g (ball c R) :=
    ⟨hg.mono ball_subset_closedBall, by rw [closure_ball c hR.ne']; exact hg.continuousOn⟩
  exact Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hR hd
    (fun w hw => hM w (sphere_subset_closedBall hw))

lemma cauchy_line {Ω : Set (V n)} {F : V n → ℂ} (hΩ : IsOpen Ω) (hF : DifferentiableOn ℂ F Ω)
    {z e : V n} (he : ‖e‖ = 1) {r M : ℝ} (hr : 0 < r) (hsub : closedBall z r ⊆ Ω)
    (hM : ∀ w ∈ closedBall z r, ‖F w‖ ≤ M) :
    ‖fderiv ℂ F z e‖ ≤ M / r ∧ ‖complexLineSecondDeriv F z e‖ ≤ 4 * M / r ^ 2 := by
  have hU : IsOpen {l : ℂ | z + l • e ∈ Ω} := hΩ.preimage (by fun_prop)
  have hg : DifferentiableOn ℂ (fun l : ℂ => F (z + l • e)) {l : ℂ | z + l • e ∈ Ω} :=
    hF.comp (by fun_prop) (fun l hl => hl)
  have hball : ∀ l ∈ closedBall (0 : ℂ) r, z + l • e ∈ closedBall z r := by
    intro l hl
    rw [mem_closedBall, dist_eq_norm] at hl ⊢
    simpa [norm_smul, he] using hl
  have hsubU : closedBall (0 : ℂ) r ⊆ {l : ℂ | z + l • e ∈ Ω} := fun l hl => hsub (hball l hl)
  have hM' : ∀ l ∈ closedBall (0 : ℂ) r, ‖F (z + l • e)‖ ≤ M := fun l hl => hM _ (hball l hl)
  have hd0 : deriv (fun l : ℂ => F (z + l • e)) 0 = fderiv ℂ F z e := by
    have h1 := deriv_slice hΩ hF (z := z) (e := e) (l := 0)
      (by simpa using hsub (mem_closedBall_self hr.le))
    simpa using h1
  refine ⟨?_, ?_⟩
  · rw [← hd0]
    exact cauchy_deriv_le hr (hg.mono hsubU) hM'
  · have hr2 : 0 < r / 2 := by positivity

    have hb2 : ∀ w ∈ closedBall (0 : ℂ) (r / 2),
        ‖deriv (fun l : ℂ => F (z + l • e)) w‖ ≤ M / (r / 2) := by
      intro w hw
      have hsub2 : closedBall w (r / 2) ⊆ closedBall (0 : ℂ) r := by
        intro l hl
        rw [mem_closedBall] at hl hw ⊢
        calc dist l 0 ≤ dist l w + dist w 0 := dist_triangle _ _ _
          _ ≤ r / 2 + r / 2 := add_le_add hl hw
          _ = r := by ring
      exact cauchy_deriv_le hr2 ((hg.mono hsubU).mono hsub2) (fun l hl => hM' l (hsub2 hl))
    have hdd := cauchy_deriv_le hr2 ((hg.deriv hU).mono
      (fun l hl => hsubU (closedBall_subset_closedBall (by linarith) hl))) hb2
    show ‖deriv (deriv fun l : ℂ => F (z + l • e)) 0‖ ≤ 4 * M / r ^ 2
    calc ‖deriv (deriv fun l : ℂ => F (z + l • e)) 0‖ ≤ M / (r / 2) / (r / 2) := hdd
      _ = 4 * M / r ^ 2 := by field_simp; ring

lemma measurable_mul_complexLineSecondDeriv {Ω : Set (V n)} {F : V n → ℂ} (hΩ : IsOpen Ω)
    (hF : DifferentiableOn ℂ F Ω) (e : V n) {χ : V n → ℂ} (hχ : Measurable χ)
    (hχΩ : ∀ z, χ z ≠ 0 → z ∈ Ω) : Measurable (fun z => χ z * complexLineSecondDeriv F z e) := by

  have hΦ : Measurable (fun w => fderiv ℂ F w e) := measurable_fderiv_apply_const ℂ F e
  have hu0 : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall fun k => Set.mem_compl_singleton_iff.2 (by positivity)⟩
  refine measurable_of_tendsto_metrizable
    (f := fun (k : ℕ) z => χ z * ((1 / ((k : ℝ) + 1))⁻¹ •
      (fderiv ℂ F (z + (1 / ((k : ℝ) + 1)) • ((1 : ℂ) • e)) e - fderiv ℂ F z e)))
    (fun k => ?_) (tendsto_pi_nhds.2 fun z => ?_)
  · refine hχ.mul ?_
    have hm := ((hΦ.comp (measurable_add_const ((1 / ((k : ℝ) + 1)) • ((1 : ℂ) • e)))).sub hΦ).const_smul
      ((1 / ((k : ℝ) + 1))⁻¹)
    exact hm
  · by_cases hz : χ z = 0
    · simp only [hz, zero_mul]
      exact tendsto_const_nhds
    · have hd := hasDerivAt_realLine_fderiv hΩ hF (hχΩ z hz) e 1
      have hs := (hd.tendsto_slope_zero.comp hu0).const_mul (χ z)
      simpa using hs

end

end ReciprocityTheory.L2DbarEstimates.C
