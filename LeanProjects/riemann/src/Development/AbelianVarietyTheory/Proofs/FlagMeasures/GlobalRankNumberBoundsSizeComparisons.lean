import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SecondLabelsNonempty

open GlobalTheory.Diag.PG Filter

noncomputable section

namespace GlobalTheory.Diag.PG.SqrtBound

theorem poly_ineq {t K a : ℝ} (ht2 : 2 ≤ t) (htK : K ≤ t) (ha : a ≤ K) : a * t + t ^ 2 ≤ t ^ 4 / 2 := by
  have ht0 : 0 ≤ t := by linarith
  have hat : a * t ≤ t * t := mul_le_mul_of_nonneg_right (ha.trans htK) ht0
  have h4 : 4 ≤ t ^ 2 := by nlinarith
  nlinarith

theorem scale_facts {eps x : ℝ} (heps : 0 < eps) (hx : 1 ≤ x) :
    Real.log x ≤ 4 * x ^ (eps / 4) / eps ∧ x ^ (eps / 2) = (x ^ (eps / 4)) ^ 2 ∧
      x ^ eps = (x ^ (eps / 4)) ^ 4 := by
  have hx0 : 0 ≤ x := by linarith
  refine ⟨?_, ?_, ?_⟩
  · have h := Real.log_le_rpow_div hx0 (by positivity : 0 < eps / 4)
    calc Real.log x ≤ x ^ (eps / 4) / (eps / 4) := h
      _ = 4 * x ^ (eps / 4) / eps := by field_simp
  · rw [← Real.rpow_mul_natCast hx0]; push_cast; ring_nf
  · rw [← Real.rpow_mul_natCast hx0]; push_cast; ring_nf

theorem exp_bound {eps A x K : ℝ} (heps : 0 < eps) (hA : 0 < A) (hx : 1 ≤ x)
    (ht2 : 2 ≤ x ^ (eps / 4)) (htK : K ≤ x ^ (eps / 4)) (hK : |Real.log A| + 40 / eps ≤ K) :
    A * x ^ 10 * Real.exp (x ^ (eps / 2)) ≤ Real.exp (x ^ eps / 2) := by
  have hx0 : 0 < x := by linarith
  obtain ⟨hlog, h2, h4⟩ := scale_facts heps hx
  set t := x ^ (eps / 4) with ht
  have hp := poly_ineq (a := |Real.log A| + 40 / eps) ht2 htK hK
  have h1 : Real.log A ≤ |Real.log A| := le_abs_self _
  have h3 : |Real.log A| ≤ |Real.log A| * t := le_mul_of_one_le_right (abs_nonneg _) (by linarith)
  have h5 : 10 * Real.log x ≤ 40 / eps * t := by
    calc 10 * Real.log x ≤ 10 * (4 * t / eps) := by linarith
      _ = 40 / eps * t := by ring
  have key : Real.log A + 10 * Real.log x + t ^ 2 ≤ t ^ 4 / 2 := by nlinarith
  have e10 : Real.exp (10 * Real.log x) = x ^ 10 := by
    rw [show (10 : ℝ) * Real.log x = Real.log (x ^ 10) by rw [Real.log_pow]; norm_num]
    exact Real.exp_log (by positivity)
  calc A * x ^ 10 * Real.exp (x ^ (eps / 2))
        = Real.exp (Real.log A + 10 * Real.log x + x ^ (eps / 2)) := by
          rw [Real.exp_add, Real.exp_add, Real.exp_log hA, e10]
    _ ≤ Real.exp (x ^ eps / 2) := Real.exp_le_exp.2 (by rw [h2, h4]; linarith)

theorem log_bound {eps C x K : ℝ} (heps : 0 < eps) (hC : 0 ≤ C) (hx : 1 ≤ x)
    (ht2 : 2 ≤ x ^ (eps / 4)) (htK : K ≤ x ^ (eps / 4)) (hK : 20 * C / eps ≤ K) :
    Real.log x * (5 * C) ≤ x ^ eps / 2 := by
  obtain ⟨hlog, -, h4⟩ := scale_facts heps hx
  set t := x ^ (eps / 4) with ht
  have ht0 : 0 ≤ t := by linarith
  have hp := poly_ineq (a := 20 * C / eps) ht2 htK hK
  have hat : 0 ≤ 20 * C / eps * t := by positivity
  have h1 : Real.log x * (5 * C) ≤ 4 * t / eps * (5 * C) :=
    mul_le_mul_of_nonneg_right hlog (by positivity)
  have h2 : 4 * t / eps * (5 * C) = 20 * C / eps * t := by ring
  rw [h4]
  nlinarith

theorem rankNums_sizes : ∀ eps CD : ℝ, 0 < eps → eps < 1 / 52 → 3 ≤ CD → ∀ C : ℝ, 0 < C → ∃ x0 : ℝ, ∀ x, x0 ≤ x →
    ∀ m f k lrd Del : ℝ, RankNums x eps CD m f k lrd Del → 1 ≤ Del ∧ C * (m * k * Del) ≤ Real.sqrt (bx x eps) ∧
      max (k ^ C) (bx x eps ^ ((1 : ℝ) / 4)) ≤ Real.sqrt (bx x eps) ∧ 12 * k * Del ≤ Real.sqrt (bx x eps) ∧
      Real.sqrt (bx x eps) ≤ bx x eps ^ 2 ∧ bx x eps ^ 2 ≤ bx x eps ^ (3 : ℝ) ∧
      (C ≤ CD → (k * f * x ^ eps) ^ C ≤ Del) := by
  intro eps CD heps _ hCD C hC
  set K0 := max (max 2 (|Real.log C| + 40 / eps)) (max (|Real.log 12| + 40 / eps) (20 * C / eps)) with hK0
  have hK0pos : 0 ≤ K0 := le_trans (by norm_num) (le_trans (le_max_left _ _) (le_max_left _ _))
  refine ⟨max 1 (K0 ^ (4 / eps)), ?_⟩
  intro x hx m f k lrd Del h
  have hx1 : 1 ≤ x := le_trans (le_max_left _ _) hx
  have hx0 : 0 < x := by linarith
  have htK0 : K0 ≤ x ^ (eps / 4) := by
    have h1 : K0 ^ (4 / eps) ≤ x := le_trans (le_max_right _ _) hx
    have h2 := Real.rpow_le_rpow (by positivity) h1 (by positivity : (0 : ℝ) ≤ eps / 4)
    rwa [← Real.rpow_mul hK0pos, show 4 / eps * (eps / 4) = (1 : ℝ) by field_simp, Real.rpow_one] at h2
  have ht2 : 2 ≤ x ^ (eps / 4) := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) htK0
  have htA : |Real.log C| + 40 / eps ≤ x ^ (eps / 4) := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) htK0
  have ht12 : |Real.log 12| + 40 / eps ≤ x ^ (eps / 4) := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) htK0
  have htC : 20 * C / eps ≤ x ^ (eps / 4) := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) htK0

  have hm1 : 1 ≤ m := le_trans (Real.one_le_rpow hx1 (by norm_num)) h.m_lo
  have hm4 : m ≤ m ^ 4 := by nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) hm1 3]
  have hf1 : 1 ≤ f := le_trans (by nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) hm1 4]) h.mf
  have hk1 : 1 ≤ k := le_trans hf1 h.fk
  have hk5 : k ≤ x ^ 5 := by
    have := h.k_hi
    rwa [show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at this
  have hm5 : m ≤ x ^ 5 := le_trans (le_trans hm4 (le_trans h.mf h.fk)) hk5
  have hxe1 : 1 ≤ x ^ eps := Real.one_le_rpow hx1 heps.le

  have hB1 : 1 ≤ k * f * x ^ eps := by
    have : 1 ≤ k * f := by nlinarith
    nlinarith
  have hDel1 : 1 ≤ Del := le_trans (Real.one_le_rpow hB1 (by linarith)) h.Del_lo
  have hDelE : Del ≤ Real.exp (x ^ (eps / 2)) :=
    (Real.log_le_iff_le_exp (by linarith)).1 h.Del_hi

  have hsq : Real.sqrt (bx x eps) = Real.exp (x ^ eps / 2) := by
    rw [Real.sqrt_eq_rpow, bx, ← Real.exp_mul]; ring_nf
  have hE0 : 0 ≤ Real.exp (x ^ (eps / 2)) := (Real.exp_pos _).le
  have hx10 : m * k ≤ x ^ 10 := by
    have : x ^ 10 = x ^ 5 * x ^ 5 := by ring
    rw [this]; exact mul_le_mul hm5 hk5 (by linarith) (by positivity)
  have hb1 : 1 ≤ bx x eps := Real.one_le_exp (by positivity)
  refine ⟨hDel1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hsq]
    calc C * (m * k * Del) ≤ C * x ^ 10 * Real.exp (x ^ (eps / 2)) := by
          rw [mul_assoc C]
          exact mul_le_mul_of_nonneg_left (mul_le_mul hx10 hDelE (by linarith) (by positivity)) hC.le
      _ ≤ Real.exp (x ^ eps / 2) := exp_bound heps hC hx1 ht2 htA le_rfl
  · rw [hsq]
    refine max_le ?_ ?_
    · have hk0 : 0 < k := by linarith
      rw [Real.rpow_def_of_pos hk0]
      refine Real.exp_le_exp.2 (le_trans ?_ (log_bound heps hC.le hx1 ht2 htC le_rfl))
      have hlk : Real.log k ≤ 5 * Real.log x := by
        have h5 := Real.log_le_log hk0 hk5
        rw [Real.log_pow] at h5; push_cast at h5; linarith
      nlinarith
    · rw [bx, ← Real.exp_mul]
      exact Real.exp_le_exp.2 (by nlinarith [Real.rpow_nonneg hx0.le eps])
  · rw [hsq]
    calc 12 * k * Del ≤ 12 * x ^ 10 * Real.exp (x ^ (eps / 2)) := by
          have hk10 : k ≤ x ^ 10 := le_trans hk5 (pow_le_pow_right₀ hx1 (by norm_num))
          rw [mul_assoc, mul_assoc (12 : ℝ)]
          exact mul_le_mul_of_nonneg_left (mul_le_mul hk10 hDelE (by linarith) (by positivity)) (by norm_num)
      _ ≤ Real.exp (x ^ eps / 2) := exp_bound heps (by norm_num) hx1 ht2 ht12 le_rfl
  · rw [hsq, bx, ← Real.exp_nat_mul]
    exact Real.exp_le_exp.2 (by push_cast; nlinarith [Real.rpow_nonneg hx0.le eps])
  · rw [show bx x eps ^ 2 = bx x eps ^ ((2 : ℕ) : ℝ) from (Real.rpow_natCast _ 2).symm]
    exact Real.rpow_le_rpow_of_exponent_le hb1 (by norm_num)
  · intro hCC
    exact le_trans (Real.rpow_le_rpow_of_exponent_le hB1 hCC) h.Del_lo

end GlobalTheory.Diag.PG.SqrtBound

end
