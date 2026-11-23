import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.HoloWeakStatement

namespace ReciprocityTheory.L2DbarEstimates.C

open MeasureTheory Metric Set Filter Topology Complex
open scoped ENNReal ContDiff

noncomputable def extCh (t : ℝ) : ℝ := Real.smoothTransition (2 - t)

theorem extCh_contDiff : ContDiff ℝ ∞ extCh :=
  Real.smoothTransition.contDiff.comp (contDiff_const.sub contDiff_id)

theorem extCh_nonneg (t : ℝ) : 0 ≤ extCh t := Real.smoothTransition.nonneg _

theorem extCh_le_one (t : ℝ) : extCh t ≤ 1 := Real.smoothTransition.le_one _

theorem extCh_of_le_one {t : ℝ} (ht : t ≤ 1) : extCh t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem extCh_of_two_le {t : ℝ} (ht : 2 ≤ t) : extCh t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem deriv_extCh_of_lt_one {t : ℝ} (ht : t < 1) : deriv extCh t = 0 := by
  have h : extCh =ᶠ[𝓝 t] fun _ => (1 : ℝ) := by
    filter_upwards [Iio_mem_nhds ht] with s hs
    exact extCh_of_le_one (le_of_lt hs)
  rw [h.deriv_eq]
  simp

theorem deriv_extCh_of_two_lt {t : ℝ} (ht : 2 < t) : deriv extCh t = 0 := by
  have h : extCh =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact extCh_of_two_le (le_of_lt hs)
  rw [h.deriv_eq]
  simp

theorem exists_deriv_extCh_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ t, ‖deriv extCh t‖ ≤ C := by
  have hc : Continuous (deriv extCh) := extCh_contDiff.continuous_deriv (by simp)
  have hs : HasCompactSupport (deriv extCh) := by
    refine HasCompactSupport.intro (isCompact_Icc (a := (1 : ℝ)) (b := 2)) ?_
    intro t ht
    rcases lt_or_ge t 1 with h1 | h1
    · exact deriv_extCh_of_lt_one h1
    · have h2 : 2 < t := by
        by_contra h2
        exact ht ⟨h1, not_lt.1 h2⟩
      exact deriv_extCh_of_two_lt h2
  obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support hs
  exact ⟨C, (norm_nonneg _).trans (hC 0), hC⟩

variable {n : ℕ}

noncomputable def extCut (F : V n → ℂ) (k : ℝ) (z : V n) : ℝ :=
  if F z = 0 then 0 else extCh (-Real.log (‖F z‖ ^ 2) / k)

theorem logCutoff_nonneg (F : V n → ℂ) (k : ℝ) (z : V n) : 0 ≤ extCut F k z := by
  unfold extCut
  split_ifs
  · exact le_rfl
  · exact extCh_nonneg _

theorem logCutoff_le_one (F : V n → ℂ) (k : ℝ) (z : V n) : extCut F k z ≤ 1 := by
  unfold extCut
  split_ifs
  · exact zero_le_one
  · exact extCh_le_one _

theorem logCutoff_eq_one {F : V n → ℂ} {k : ℝ} (hk : 0 < k) {z : V n} (hz : F z ≠ 0)
    (h : -Real.log (‖F z‖ ^ 2) ≤ k) : extCut F k z = 1 := by
  simp only [extCut, hz, if_false]
  exact extCh_of_le_one ((div_le_one hk).2 h)

theorem logCutoff_eventuallyEq_zero {F : V n → ℂ} {k : ℝ} (hk : 0 < k) {z : V n}
    (hFc : ContinuousAt F z) (hz : F z = 0) : extCut F k =ᶠ[𝓝 z] fun _ => (0 : ℝ) := by
  have hball : Metric.ball (0 : ℂ) (Real.exp (-k)) ∈ 𝓝 (F z) := by
    rw [hz]
    exact Metric.ball_mem_nhds _ (Real.exp_pos _)
  filter_upwards [hFc.preimage_mem_nhds hball] with w hw
  have hw' : ‖F w‖ < Real.exp (-k) := by simpa using hw
  unfold extCut
  split_ifs with h0
  · rfl
  · apply extCh_of_two_le
    have hpos : 0 < ‖F w‖ := norm_pos_iff.2 h0
    have hlog : Real.log ‖F w‖ < -k := by
      have := Real.log_lt_log hpos hw'
      rwa [Real.log_exp] at this
    rw [le_div_iff₀ hk, Real.log_pow]
    push_cast
    linarith

theorem contDiffAt_logCutoff {F : V n → ℂ} {k : ℝ} (hk : 0 < k) {z : V n}
    (hF : ContDiffAt ℝ ∞ F z) : ContDiffAt ℝ ∞ (extCut F k) z := by
  by_cases h0 : F z = 0
  · exact contDiffAt_const.congr_of_eventuallyEq
      (logCutoff_eventuallyEq_zero hk hF.continuousAt h0)
  · have hin : ContDiffAt ℝ ∞ (fun w => -Real.log (‖F w‖ ^ 2) / k) z := by
      have h2 : ContDiffAt ℝ ∞ (fun w => ‖F w‖ ^ 2) z := hF.norm_sq ℝ
      have hne : ‖F z‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.2 h0)
      exact ((h2.log hne).neg).div_const k
    have hcomp : ContDiffAt ℝ ∞ (fun w => extCh (-Real.log (‖F w‖ ^ 2) / k)) z :=
      extCh_contDiff.contDiffAt.comp z hin
    refine hcomp.congr_of_eventuallyEq ?_
    filter_upwards [hF.continuousAt.eventually_ne h0] with w hw
    simp [extCut, hw]

theorem isTest_logCutoff_mul {Ω : Set (V n)} {F : V n → ℂ}
    (hsm : ∀ z ∈ Ω, ContDiffAt ℝ ∞ F z) {k : ℝ} (hk : 0 < k) {g : V n → ℂ} (hg : IsTest Ω g) :
    IsTest (Ω \ {z | F z = 0}) (fun z => (extCut F k z : ℂ) * g z) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro z
    by_cases hz : z ∈ tsupport g
    · have hzΩ : z ∈ Ω := hg.2.2 hz
      have hc : ContDiffAt ℝ ∞ (fun w => (extCut F k w : ℂ)) z :=
        ofRealCLM.contDiff.contDiffAt.comp z (contDiffAt_logCutoff hk (hsm z hzΩ))
      exact hc.mul (hg.1.contDiffAt)
    · have hg0 : g =ᶠ[𝓝 z] 0 := (notMem_tsupport_iff_eventuallyEq).1 hz
      refine (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ => (0 : ℂ)) z).congr_of_eventuallyEq ?_
      filter_upwards [hg0] with w hw
      simp [hw]
  · exact hg.2.1.mul_left
  · intro z hz
    have hzg : z ∈ tsupport g := tsupport_mul_subset_right hz
    have hzΩ : z ∈ Ω := hg.2.2 hzg
    refine ⟨hzΩ, ?_⟩
    intro hF0
    have hF0' : F z = 0 := hF0
    have hcut := logCutoff_eventuallyEq_zero hk (hsm z hzΩ).continuousAt hF0'
    have hprod : (fun w => (extCut F k w : ℂ) * g w) =ᶠ[𝓝 z] 0 := by
      filter_upwards [hcut] with w hw
      simp [hw]
    exact ((notMem_tsupport_iff_eventuallyEq).2 hprod) hz

theorem fderiv_logCutoff {F : V n → ℂ} {k : ℝ} {z : V n}
    (hF : DifferentiableAt ℝ F z) (hz : F z ≠ 0) :
    fderiv ℝ (extCut F k) z = deriv extCh (-Real.log (‖F z‖ ^ 2) / k) •
      ((-k⁻¹) • fderiv ℝ (fun w => Real.log (‖F w‖ ^ 2)) z) := by
  have hne : ‖F z‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.2 hz)
  have hL : HasFDerivAt (fun w => Real.log (‖F w‖ ^ 2))
      (fderiv ℝ (fun w => Real.log (‖F w‖ ^ 2)) z) z :=
    (((hF.norm_sq ℝ).log hne)).hasFDerivAt
  have e : (fun w => -Real.log (‖F w‖ ^ 2) / k) =
      fun w => (-k⁻¹) • Real.log (‖F w‖ ^ 2) := by
    funext w
    simp only [smul_eq_mul]
    ring
  have hh : HasFDerivAt (fun w => -Real.log (‖F w‖ ^ 2) / k)
      ((-k⁻¹) • fderiv ℝ (fun w => Real.log (‖F w‖ ^ 2)) z) z := by
    rw [e]
    exact hL.const_smul (-k⁻¹ : ℝ)
  have hd : HasDerivAt extCh (deriv extCh (-Real.log (‖F z‖ ^ 2) / k))
      (-Real.log (‖F z‖ ^ 2) / k) :=
    ((extCh_contDiff.differentiable (by simp)) _).hasDerivAt
  have hcomp := hd.comp_hasFDerivAt z hh
  have heq : extCut F k =ᶠ[𝓝 z] extCh ∘ fun w => -Real.log (‖F w‖ ^ 2) / k := by
    filter_upwards [hF.continuousAt.eventually_ne hz] with w hw
    simp [extCut, hw]
  rw [heq.fderiv_eq]
  exact hcomp.fderiv

theorem norm_fderiv_logCutoff_le {F : V n → ℂ} {k C : ℝ} (hk : 0 < k)
    (hC : ∀ t, ‖deriv extCh t‖ ≤ C) {z : V n} (hF : DifferentiableAt ℝ F z) (hz : F z ≠ 0) :
    ‖fderiv ℝ (extCut F k) z‖ ≤ C * k⁻¹ * ‖fderiv ℝ (fun w => Real.log (‖F w‖ ^ 2)) z‖ := by
  rw [fderiv_logCutoff hF hz, norm_smul, norm_smul, norm_neg, norm_inv,
    Real.norm_of_nonneg hk.le, ← mul_assoc]
  gcongr
  exact hC _

theorem fderiv_logCutoff_eq_zero {F : V n → ℂ} {k : ℝ} (hk : 0 < k) {z : V n}
    (hF : DifferentiableAt ℝ F z) (hz : F z ≠ 0)
    (h : ¬ (k ≤ -Real.log (‖F z‖ ^ 2) ∧ -Real.log (‖F z‖ ^ 2) ≤ 2 * k)) :
    fderiv ℝ (extCut F k) z = 0 := by
  rw [fderiv_logCutoff hF hz]
  set a := -Real.log (‖F z‖ ^ 2) with ha
  have hd : deriv extCh (a / k) = 0 := by
    by_cases h1 : k ≤ a
    · have h2 : 2 * k < a := by
        push_neg at h
        exact h h1
      exact deriv_extCh_of_two_lt ((lt_div_iff₀ hk).2 (by linarith))
    · push_neg at h1
      exact deriv_extCh_of_lt_one ((div_lt_one hk).2 h1)
  rw [hd, zero_smul]

theorem dbarDir_extensionCutoff_mul {F g : V n → ℂ} {k : ℝ} {z : V n} (v : V n)
    (hc : DifferentiableAt ℝ (extCut F k) z) (hg : DifferentiableAt ℝ g z) :
    dbarDir (fun w => (extCut F k w : ℂ) * g w) z v =
      (extCut F k z : ℂ) * dbarDir g z v + g z * ((fderiv ℝ (extCut F k) z (I • v) : ℂ) -
        I * (fderiv ℝ (extCut F k) z v : ℂ)) := by
  have hcC : HasFDerivAt (fun w => (extCut F k w : ℂ))
      (ofRealCLM.comp (fderiv ℝ (extCut F k) z)) z :=
    ofRealCLM.hasFDerivAt.comp z hc.hasFDerivAt
  unfold dbarDir
  have hm : HasFDerivAt (fun w => (extCut F k w : ℂ) * g w)
      ((extCut F k z : ℂ) • fderiv ℝ g z + g z • (ofRealCLM.comp (fderiv ℝ (extCut F k) z))) z :=
    hcC.mul hg.hasFDerivAt
  rw [hm.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    ContinuousLinearMap.comp_apply, ofRealCLM_apply]
  ring

end ReciprocityTheory.L2DbarEstimates.C
