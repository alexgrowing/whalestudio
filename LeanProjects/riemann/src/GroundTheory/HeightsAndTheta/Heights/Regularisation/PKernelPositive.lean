import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Regularisation.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Regular

open Metric Filter Topology Matrix

noncomputable section

namespace KernelPositive

def cquad {g : ℕ} (v : Fin g → ℝ) (M : Matrix (Fin g) (Fin g) ℂ) : ℂ :=
  (fun k => (v k : ℂ)) ⬝ᵥ M *ᵥ fun k => (v k : ℂ)

theorem cquad_im {g : ℕ} (v : Fin g → ℝ) (M : Matrix (Fin g) (Fin g) ℂ) :
    (cquad v M).im = v ⬝ᵥ (M.map Complex.im *ᵥ v) := by
  simp [cquad, dotProduct, mulVec, Complex.im_sum, Complex.mul_im]

theorem intMat_mulVec_ofReal {g : ℕ} (B : Matrix (Fin g) (Fin g) ℤ) (v : Fin g → ℝ)
    (h : B.map (Int.cast : ℤ → ℝ) *ᵥ v = 0) :
    B.map (Int.cast : ℤ → ℂ) *ᵥ (fun k => (v k : ℂ)) = 0 := by
  funext k
  have hk := congrFun h k
  simp only [mulVec, dotProduct, Matrix.map_apply, Pi.zero_apply] at hk ⊢
  exact_mod_cast hk

theorem im_pos_of_punctured {h : ℂ → ℂ} (hh : AnalyticAt ℂ h 0)
    (hpos : ∀ᶠ t in 𝓝[≠] (0 : ℂ), 0 < (h t).im) : 0 < (h 0).im := by
  by_contra hle
  rw [not_lt] at hle
  rcases hh.eventually_constant_or_nhds_le_map_nhds with hc | hmap
  · obtain ⟨t, ht, hte⟩ := (hpos.and (nhdsWithin_le_nhds hc)).exists
    rw [hte] at ht
    linarith
  · have hH : {w : ℂ | 0 < w.im ∨ w = h 0} ∈ 𝓝 (h 0) := by
      apply hmap
      rw [Filter.mem_map]
      filter_upwards [eventually_nhdsWithin_iff.mp hpos] with t ht
      by_cases h0 : t = 0
      · right
        rw [h0]
      · left
        exact ht h0
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hH
    have hmem : h 0 - ((ε / 2 : ℝ) : ℂ) * Complex.I ∈ ball (h 0) ε := by
      rw [mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_mul, Complex.norm_I, mul_one,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
      linarith
    rcases hball hmem with hw | hw
    · simp at hw
      linarith
    · have := congrArg Complex.im hw
      simp at this
      linarith

theorem pos_of_punctured {n a g : ℕ} (P : PeriodPolydisc n a g)
    {T0 : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ} (hT : P.IsTau0Ext T0) {v : Fin g → ℝ}
    (hv : v ≠ 0) (hB : ∀ i, (P.B i).map (Int.cast : ℤ → ℝ) *ᵥ v = 0) {z : Fin n → ℂ}
    (hz : z ∈ ball (0 : Fin n → ℂ) 1) (hz0 : ∀ k, z k ≠ 0) :
    0 < (cquad v (T0 z)).im := by
  have hzk : ∀ k, ‖z k‖ < 1 := fun k => (norm_le_pi_norm z k).trans_lt (mem_ball_zero_iff.mp hz)
  have hw : logLift a z ∈ logCover P.a_le := by
    refine ⟨fun i => ?_, fun k hk => ?_⟩
    · have hi : (Fin.castLE P.a_le i).val < a := i.isLt
      simp only [logLift, if_pos hi, Complex.log_re]
      exact Real.log_neg (norm_pos_iff.mpr (hz0 _)) (hzk _)
    · simp only [logLift, if_neg (not_lt.mpr hk)]
      exact hzk k
  have hexp : expCover a (logLift a z) = z := by
    funext k
    by_cases hk : k.val < a
    · simp [expCover, logLift, hk, Complex.exp_log (hz0 k)]
    · simp [expCover, logLift, hk]
  have hT0 : T0 z = P.tau0 (logLift a z) := by
    rw [(hT.2 _ hw), hexp]
  have hsum : (∑ i : Fin a, (logLift a z (Fin.castLE P.a_le i) / (2 * Real.pi * Complex.I)) •
      (P.B i).map (Int.cast : ℤ → ℂ)) *ᵥ (fun k => (v k : ℂ)) = 0 := by
    refine Finset.sum_induction _ (fun N => N *ᵥ (fun k => (v k : ℂ)) = 0)
      (fun A B hA hB => by rw [add_mulVec, hA, hB, add_zero]) (zero_mulVec _) (fun i _ => ?_)
    rw [smul_mulVec, intMat_mulVec_ofReal _ _ (hB i), smul_zero]
  have hq : cquad v (T0 z) = cquad v (P.τ (logLift a z)) := by
    rw [hT0, cquad, cquad, PeriodPolydisc.tau0, sub_mulVec, hsum, sub_zero]
  rw [hq, cquad_im]
  simpa using (P.im_posDef _ hw).dotProduct_mulVec_pos hv

def line {n : ℕ} (z : Fin n → ℂ) (t : ℂ) : Fin n → ℂ := z + t • fun _ => (1 : ℂ)

theorem line_apply {n : ℕ} (z : Fin n → ℂ) (t : ℂ) (k : Fin n) : line z t k = z k + t := by
  simp [line]

end KernelPositive

open KernelPositive in

theorem kernelPositive_statement : KernelPositive.Statement := by
  intro n a g P T0 hT v hv hB z hz
  rw [← cquad_im]
  have hLa : AnalyticAt ℂ (line z) 0 :=
    analyticAt_const.add (analyticAt_id.smul analyticAt_const)
  have hL0 : line z 0 = z := by simp [line]
  have hG : AnalyticAt ℂ (fun t => cquad v (T0 (line z t))) 0 := by
    have h : (fun t => cquad v (T0 (line z t))) =
        ∑ p, ∑ q, fun t => (v p : ℂ) * (T0 (line z t) p q * (v q : ℂ)) := by
      funext t
      simp [cquad, dotProduct, mulVec, Finset.sum_apply, Finset.mul_sum]
    rw [h]
    refine Finset.analyticAt_sum _ fun p _ => Finset.analyticAt_sum _ fun q _ => ?_
    exact analyticAt_const.mul
      ((AnalyticAt.comp_of_eq (hT.1 p q z hz) hLa hL0).mul analyticAt_const)
  have hball : ∀ᶠ t in 𝓝 (0 : ℂ), line z t ∈ ball (0 : Fin n → ℂ) 1 :=
    hLa.continuousAt.preimage_mem_nhds (isOpen_ball.mem_nhds (by rw [hL0]; exact hz))
  have hne : ∀ᶠ t in 𝓝[≠] (0 : ℂ), ∀ k, line z t k ≠ 0 := by
    refine Filter.eventually_all.mpr fun k => ?_
    by_cases hzk : z k = 0
    · filter_upwards [self_mem_nhdsWithin] with t ht
      rw [line_apply, hzk, zero_add]
      exact ht
    · have hc : ContinuousAt (fun t : ℂ => z k + t) 0 :=
        (continuous_const.add continuous_id).continuousAt
      have := hc.eventually_ne (by simpa using hzk)
      exact nhdsWithin_le_nhds (this.mono fun t ht => by rw [line_apply]; exact ht)
  have hpos : ∀ᶠ t in 𝓝[≠] (0 : ℂ), 0 < (cquad v (T0 (line z t))).im := by
    filter_upwards [nhdsWithin_le_nhds hball, hne] with t ht1 ht2
    exact pos_of_punctured P hT hv hB ht1 ht2
  have := im_pos_of_punctured hG hpos
  simpa only [hL0] using this

theorem KernelPositive.proof (_h0 : Tau0Holomorphic.Statement) : KernelPositive.Statement :=
  kernelPositive_statement

end

end GroundTheory.Heights₂.Heights.Regular
