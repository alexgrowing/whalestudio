import Formalism.ZeroFreeRegion.SmallHeightLogDeriv

open Complex Metric

noncomputable section

namespace Formalism.ZF

lemma zfo_ball_facts {σ τ : ℝ} {w : ℂ} (hw : w ∈ closedBall ((σ : ℂ) + τ * I) (1 / 2)) :
    |w.re - σ| ≤ 1 / 2 ∧ |w.im - τ| ≤ 1 / 2 ∧ ‖w‖ ≤ |σ| + |τ| + 1 / 2 := by
  rw [mem_closedBall, dist_eq_norm] at hw
  have hre : (w - ((σ : ℂ) + τ * I)).re = w.re - σ := by simp
  have him : (w - ((σ : ℂ) + τ * I)).im = w.im - τ := by simp
  refine ⟨?_, ?_, ?_⟩
  · rw [← hre]
    exact (Complex.abs_re_le_norm _).trans hw
  · rw [← him]
    exact (Complex.abs_im_le_norm _).trans hw
  · have hc : ‖(σ : ℂ) + τ * I‖ ≤ |σ| + |τ| := by
      refine (norm_add_le _ _).trans ?_
      simp [Complex.norm_real]
    calc ‖w‖ = ‖(w - ((σ : ℂ) + τ * I)) + ((σ : ℂ) + τ * I)‖ := by rw [sub_add_cancel]
      _ ≤ ‖w - ((σ : ℂ) + τ * I)‖ + ‖(σ : ℂ) + τ * I‖ := norm_add_le _ _
      _ ≤ 1 / 2 + (|σ| + |τ|) := add_le_add hw hc
      _ = |σ| + |τ| + 1 / 2 := by ring

lemma zfo_ball_ne_one {σ τ : ℝ} (hτ : 3 ≤ |τ|) {w : ℂ}
    (hw : w ∈ closedBall ((σ : ℂ) + τ * I) (1 / 2)) : w ≠ 1 ∧ 5 / 2 ≤ |w.im| := by
  obtain ⟨-, him, -⟩ := zfo_ball_facts hw
  have h : 5 / 2 ≤ |w.im| := by
    have h' := abs_sub_abs_le_abs_sub τ w.im
    rw [abs_sub_comm] at h'
    linarith
  refine ⟨fun h1 => ?_, h⟩
  norm_num [h1] at h

lemma zfo_diff_ball {σ τ : ℝ} (hτ : 3 ≤ |τ|) :
    DifferentiableOn ℂ riemannZeta (closedBall ((σ : ℂ) + τ * I) (1 / 2)) := by
  intro w hw
  exact (differentiableAt_riemannZeta (zfo_ball_ne_one hτ hw).1).differentiableWithinAt

lemma zfo_growth_ball (hG : ZetaGrowth) {σ τ T : ℝ} (hσ1 : 1 < σ) (hσ2 : σ ≤ 2) (hτ : 3 ≤ |τ|)
    (hτT : |τ| ≤ 2 * T) {w : ℂ} (hw : w ∈ closedBall ((σ : ℂ) + τ * I) (1 / 2)) :
    ‖riemannZeta w‖ ≤ 6 * (T + 2) := by
  obtain ⟨hre, -, hn⟩ := zfo_ball_facts hw
  obtain ⟨hne, him2⟩ := zfo_ball_ne_one hτ hw
  have hre' : 1 / 2 < w.re := by
    have := (abs_le.mp hre).1
    linarith
  have h1 : 5 / 2 ≤ ‖w - 1‖ := by
    have h' : |(w - 1).im| ≤ ‖w - 1‖ := Complex.abs_im_le_norm _
    simp only [Complex.sub_im, Complex.one_im, sub_zero] at h'
    linarith
  have hinv1 : 1 / ‖w - 1‖ ≤ 2 / 5 := by
    rw [div_le_iff₀ (by linarith)]
    linarith
  have hinv2 : 1 / w.re ≤ 2 := by
    rw [div_le_iff₀ (by linarith)]
    linarith
  have hσabs : |σ| = σ := abs_of_pos (by linarith)
  have hnw : ‖w‖ ≤ 2 * T + 5 / 2 := by
    rw [hσabs] at hn
    linarith
  have hc0 : 0 ≤ 1 + 1 / w.re := by
    have : 0 < 1 / w.re := one_div_pos.mpr (by linarith)
    linarith
  have hprod : ‖w‖ * (1 + 1 / w.re) ≤ (2 * T + 5 / 2) * 3 :=
    mul_le_mul hnw (by linarith) hc0 (by linarith [abs_nonneg τ])
  have hg := hG w (by linarith) hne
  linarith

lemma zfo_M_bound (hG : ZetaGrowth) (hI : ZetaInvBound) {σ τ T : ℝ} (hσ1 : 1 < σ) (hσ2 : σ ≤ 2)
    (hσK : 2 / (σ - 1) ≤ 20000 * (T + 2)) (hT : 3 ≤ T) (hτ : 3 ≤ |τ|) (hτT : |τ| ≤ 2 * T) :
    ∀ w ∈ closedBall ((σ : ℂ) + τ * I) (1 / 2),
      ‖riemannZeta w‖ ≤ (T + 2) ^ 10 * ‖riemannZeta ((σ : ℂ) + τ * I)‖ := by
  intro w hw
  have hzw := zfo_growth_ball hG hσ1 hσ2 hτ hτT hw
  set s : ℂ := (σ : ℂ) + τ * I with hs
  have hsre : s.re = σ := by simp [hs]
  have hs1 : 1 < s.re := by rw [hsre]; exact hσ1
  have hinv := hI s hs1
  rw [hsre] at hinv
  have hσ1' : 0 < σ - 1 := by linarith
  have hA : 0 < T + 2 := by linarith
  have ha0 : 0 < ‖riemannZeta s‖ := norm_pos_iff.mpr (riemannZeta_ne_zero_of_one_lt_re hs1)
  have h1 : 1 ≤ ‖riemannZeta s‖ * (σ / (σ - 1)) :=
    calc (1 : ℝ) = ‖riemannZeta s‖ * ‖riemannZeta s‖⁻¹ := (mul_inv_cancel₀ ha0.ne').symm
      _ ≤ ‖riemannZeta s‖ * (σ / (σ - 1)) := mul_le_mul_of_nonneg_left hinv ha0.le
  rw [mul_div_assoc', le_div_iff₀ hσ1'] at h1
  have h3 : σ - 1 ≤ 2 * ‖riemannZeta s‖ := by nlinarith
  have h4 : 2 ≤ 20000 * (T + 2) * (σ - 1) := by
    rwa [div_le_iff₀ hσ1'] at hσK
  have h5 : 1 ≤ 20000 * (T + 2) * ‖riemannZeta s‖ := by
    have := mul_le_mul_of_nonneg_left h3 (by linarith : (0 : ℝ) ≤ 10000 * (T + 2))
    nlinarith
  have h8 : (5 : ℝ) ^ 8 ≤ (T + 2) ^ 8 := pow_le_pow_left₀ (by norm_num) (by linarith) 8
  have h6 : 120000 * (T + 2) ^ 2 ≤ (T + 2) ^ 10 := by
    have e : (T + 2) ^ 10 = (T + 2) ^ 2 * (T + 2) ^ 8 := by ring
    have := mul_le_mul_of_nonneg_left h8 (sq_nonneg (T + 2))
    rw [e]
    norm_num at this ⊢
    nlinarith [sq_nonneg (T + 2)]
  calc ‖riemannZeta w‖ ≤ 6 * (T + 2) := hzw
    _ ≤ 6 * (T + 2) * (20000 * (T + 2) * ‖riemannZeta s‖) := le_mul_of_one_le_right (by linarith) h5
    _ = 120000 * (T + 2) ^ 2 * ‖riemannZeta s‖ := by ring
    _ ≤ (T + 2) ^ 10 * ‖riemannZeta s‖ := mul_le_mul_of_nonneg_right h6 ha0.le

end Formalism.ZF
