import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsRootOne
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRootBallOfAnalyticOrderDvdStatement
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

namespace GlobalTheory.UHPRoot

noncomputable def cen (k : ℕ) : ℂ := ((k : ℂ) + 2) * Complex.I

noncomputable def rad (k : ℕ) : ℝ := ((k : ℝ) + 2) - 1 / ((k : ℝ) + 2)

theorem rad_pos (k : ℕ) : 0 < rad k := by
  unfold rad
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have h : 1 / ((k : ℝ) + 2) < 1 := by
    rw [div_lt_one (by positivity)]; linarith
  linarith

theorem cen_im (k : ℕ) : (cen k).im = (k : ℝ) + 2 := by simp [cen]
theorem cen_re (k : ℕ) : (cen k).re = 0 := by simp [cen]

theorem closedBall_sub (k : ℕ) : Metric.closedBall (cen k) (rad k) ⊆ Hs := by
  intro z hz
  rw [Metric.mem_closedBall, dist_eq_norm] at hz
  have h1 := Complex.abs_im_le_norm (z - cen k)
  have h2 : (z - cen k).im = z.im - ((k : ℝ) + 2) := by rw [Complex.sub_im, cen_im]
  rw [h2] at h1
  have h3 : 0 < 1 / ((k : ℝ) + 2) := by positivity
  show 0 < z.im
  unfold rad at hz
  have := neg_abs_le (z.im - ((k : ℝ) + 2))
  linarith

theorem ball_mono : Monotone (fun k : ℕ => Metric.ball (cen k) (rad k)) := by
  refine monotone_nat_of_le_succ fun k => Metric.ball_subset_ball' ?_
  have hd : cen k - cen (k + 1) = -Complex.I := by
    simp only [cen]; push_cast; ring
  rw [dist_eq_norm, hd, norm_neg, Complex.norm_I]
  unfold rad
  push_cast
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have : 1 / ((k : ℝ) + 1 + 2) ≤ 1 / ((k : ℝ) + 2) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  linarith

theorem cover (z : ℂ) (hz : z ∈ Hs) : ∃ k : ℕ, z ∈ Metric.ball (cen k) (rad k) := by
  have hy : 0 < z.im := hz
  obtain ⟨k, hk⟩ := exists_nat_gt ((z.re ^ 2 + z.im ^ 2 + 2) / (2 * z.im))
  refine ⟨k, ?_⟩
  rw [Metric.mem_ball, dist_eq_norm]
  set a : ℝ := (k : ℝ) + 2 with ha
  have hapos : 0 < a := by positivity
  have hka : (k : ℝ) < a := by linarith
  have h1 : z.re ^ 2 + z.im ^ 2 + 2 < 2 * z.im * a := by
    have := (div_lt_iff₀ (by positivity : (0:ℝ) < 2 * z.im)).1 (hk.trans hka)
    linarith
  have hsq : ‖z - cen k‖ ^ 2 = z.re ^ 2 + (z.im - a) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, cen_re, cen_im]
    ring
  have hrad : rad k = a - 1 / a := rfl
  have hinv : a * (1 / a) = 1 := by field_simp
  have hlt : ‖z - cen k‖ ^ 2 < rad k ^ 2 := by
    rw [hsq, hrad]
    nlinarith [sq_nonneg (1 / a)]
  exact lt_of_pow_lt_pow_left₀ 2 (rad_pos k).le hlt

theorem eqOn_of_pow_eq {D : Set ℂ} (hD : IsOpen D) (hc : IsPreconnected D) {m : ℕ} (hm : 0 < m)
    {f g : ℂ → ℂ} (hf : DifferentiableOn ℂ f D) (hg : DifferentiableOn ℂ g D)
    {z0 : ℂ} (hz0 : z0 ∈ D) (hfg0 : f z0 = g z0) (hne : f z0 ≠ 0)
    (hpow : ∀ z ∈ D, f z ^ m = g z ^ m) : Set.EqOn f g D := by
  have hfc : ContinuousAt f z0 := (hf.differentiableAt (hD.mem_nhds hz0)).continuousAt
  have hgc : ContinuousAt g z0 := (hg.differentiableAt (hD.mem_nhds hz0)).continuousAt
  set S : ℂ → ℂ := fun z => ∑ i ∈ Finset.range m, f z ^ i * g z ^ (m - 1 - i) with hS
  have hSc : ContinuousAt S z0 := by
    simp only [hS]; fun_prop
  have hS0 : S z0 ≠ 0 := by
    have : S z0 = (m : ℂ) * f z0 ^ (m - 1) := by
      simp only [hS, ← hfg0]
      rw [Finset.sum_congr rfl (g := fun _ => f z0 ^ (m - 1))]
      · simp
      · intro i hi
        rw [← pow_add]
        congr 1
        have := Finset.mem_range.1 hi
        omega
    rw [this]
    exact mul_ne_zero (by exact_mod_cast hm.ne') (pow_ne_zero _ hne)
  have hev : f =ᶠ[nhds z0] g := by
    filter_upwards [hSc.eventually_ne hS0, hD.mem_nhds hz0] with z hz hzD
    have key : S z * (f z - g z) = f z ^ m - g z ^ m := by
      simp only [hS]; exact geom_sum₂_mul (f z) (g z) m
    rw [hpow z hzD, sub_self] at key
    exact sub_eq_zero.1 ((mul_eq_zero.1 key).resolve_left hz)
  exact (hf.analyticOnNhd hD).eqOn_of_preconnected_of_eventuallyEq (hg.analyticOnNhd hD) hc hz0 hev

end GlobalTheory.UHPRoot

open GlobalTheory.UHPRoot in

theorem GlobalTheory.KZ.H3.uhp_root : ∀ (h : ℂ → ℂ) (m : ℕ), 0 < m → DifferentiableOn ℂ h Hs →
    (∀ τ ∈ Hs, ∃ k : ℕ, analyticOrderAt h τ = ((m * k : ℕ) : ℕ∞)) →
    ∃ r : ℂ → ℂ, DifferentiableOn ℂ r Hs ∧ ∀ z ∈ Hs, r z ^ m = h z := by
  classical
  intro h m hm hd hord
  have hHo : IsOpen Hs := isOpen_lt continuous_const Complex.continuous_im
  have han : AnalyticOnNhd ℂ h Hs := hd.analyticOnNhd hHo
  have hr : ∀ k : ℕ, ∃ r : ℂ → ℂ, DifferentiableOn ℂ r (Metric.ball (cen k) (rad k)) ∧
      ∀ z ∈ Metric.ball (cen k) (rad k), r z ^ m = h z := fun k =>
    GlobalTheory.T.exists_root_ball_of_analyticOrder_dvd h m (cen k) (rad k) hm (rad_pos k) (han.mono (closedBall_sub k))
      (fun τ hτ => hord τ (closedBall_sub k hτ))
  choose r hrd hrp using hr

  have hc0 : cen 0 ∈ Hs := closedBall_sub 0 (Metric.mem_closedBall_self (rad_pos 0).le)
  obtain ⟨k0, hk0⟩ := hord (cen 0) hc0
  have hnt : ¬ ∀ᶠ z in nhds (cen 0), h z = 0 := by
    rw [← analyticOrderAt_eq_top, hk0]; exact ENat.coe_ne_top _
  obtain ⟨z0, hz0h, hz0D⟩ := ((Filter.not_eventually.1 hnt).and_eventually
    (Metric.ball_mem_nhds (cen 0) (rad_pos 0))).exists
  obtain ⟨w0, hw0⟩ := IsAlgClosed.exists_pow_nat_eq (h z0) hm
  have hw0ne : w0 ≠ 0 := by
    rintro rfl; rw [zero_pow hm.ne'] at hw0; exact hz0h hw0.symm
  have hz0k : ∀ k, z0 ∈ Metric.ball (cen k) (rad k) := fun k => ball_mono (Nat.zero_le k) hz0D
  have hrk0 : ∀ k, r k z0 ≠ 0 := by
    intro k h0; have := hrp k z0 (hz0k k); rw [h0, zero_pow hm.ne'] at this; exact hz0h this.symm

  set r' : ℕ → ℂ → ℂ := fun k z => (w0 / r k z0) * r k z with hr'
  have hr'd : ∀ k, DifferentiableOn ℂ (r' k) (Metric.ball (cen k) (rad k)) := fun k =>
    (differentiableOn_const _).mul (hrd k)
  have hr'p : ∀ k, ∀ z ∈ Metric.ball (cen k) (rad k), r' k z ^ m = h z := by
    intro k z hz
    simp only [hr', mul_pow, div_pow, hw0, hrp k z hz, hrp k z0 (hz0k k)]
    rw [div_self hz0h, one_mul]
  have hr'0 : ∀ k, r' k z0 = w0 := by
    intro k; simp only [hr']; rw [div_mul_cancel₀ _ (hrk0 k)]
  have agree_le : ∀ j k, j ≤ k → Set.EqOn (r' j) (r' k) (Metric.ball (cen j) (rad j)) := by
    intro j k hjk
    refine eqOn_of_pow_eq Metric.isOpen_ball (convex_ball _ _).isPreconnected hm (hr'd j)
      ((hr'd k).mono (ball_mono hjk)) (hz0k j) (by rw [hr'0, hr'0]) (by rw [hr'0]; exact hw0ne) ?_
    intro z hz; rw [hr'p j z hz, hr'p k z (ball_mono hjk hz)]
  have agree : ∀ j k w, w ∈ Metric.ball (cen j) (rad j) → w ∈ Metric.ball (cen k) (rad k) →
      r' j w = r' k w := by
    intro j k w hj hk
    rcases le_total j k with hjk | hkj
    · exact agree_le j k hjk hj
    · exact (agree_le k j hkj hk).symm
  choose N hN using cover
  let R : ℂ → ℂ := fun z => if hz : z ∈ Hs then r' (N z hz) z else 0
  refine ⟨R, ?_, ?_⟩
  · intro z hz
    have hzk := hN z hz
    have hev : R =ᶠ[nhds z] r' (N z hz) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hzk] with w hw
      have hwH : w ∈ Hs := closedBall_sub _ (Metric.ball_subset_closedBall hw)
      simp only [R, dif_pos hwH]
      exact agree _ _ w (hN w hwH) hw
    exact (((hr'd _).differentiableAt (Metric.isOpen_ball.mem_nhds hzk)).congr_of_eventuallyEq
      hev).differentiableWithinAt
  · intro z hz
    simp only [R, dif_pos hz]
    exact hr'p _ z (hN z hz)
