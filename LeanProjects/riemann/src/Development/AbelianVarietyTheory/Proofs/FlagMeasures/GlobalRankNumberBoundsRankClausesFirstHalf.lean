import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SecondLabelsNonempty

namespace GlobalTheory.Diag.PG

theorem rankNums_first_half : ∀ eps CD : ℝ, 0 < eps → eps < 1 / 52 → 3 ≤ CD → ∀ C : ℝ, ∃ x0 : ℝ, ∀ x, x0 ≤ x →
    ∀ m f k lrd Del : ℝ, RankNums x eps CD m f k lrd Del → C * m ^ 5 * f * x ^ eps ≤ k ∧
      Real.log f ≤ Real.sqrt (m / 2 - 1) ∧ C * x ^ eps ≤ f * Real.log k ∧ C * (m ^ 2 * x ^ eps) ≤ k ∧ C ≤ m ∧
      C * x ^ eps ≤ m - 1 ∧ C ≤ k ∧ 1 < x ^ eps := by
  intro eps CD heps heps' _ C
  set C1 : ℝ := max C 2 with hC1
  have hCC1 : C ≤ C1 := le_max_left _ _
  have hC12 : 2 ≤ C1 := le_max_right _ _
  have e1 : ∀ᶠ x : ℝ in Filter.atTop, C1 ≤ x ^ (eps / 2) :=
    (tendsto_rpow_atTop (by linarith)).eventually_ge_atTop C1
  have e2 : ∀ᶠ x : ℝ in Filter.atTop, C1 + 1 ≤ x ^ ((1 : ℝ) / 52) :=
    (tendsto_rpow_atTop (by norm_num)).eventually_ge_atTop (C1 + 1)
  have e3 : ∀ᶠ x : ℝ in Filter.atTop, (200 : ℝ) ≤ x ^ ((1 : ℝ) / 16) :=
    (tendsto_rpow_atTop (by norm_num)).eventually_ge_atTop 200
  have e4 : ∀ᶠ x : ℝ in Filter.atTop, (2 : ℝ) ≤ x := Filter.eventually_ge_atTop 2
  obtain ⟨x0, hx0⟩ := Filter.eventually_atTop.1 (e1.and (e2.and (e3.and e4)))
  refine ⟨x0, fun x hx m f k lrd Del h => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := hx0 x hx
  have hx0' : (0 : ℝ) ≤ x := by linarith
  have hx1 : (1 : ℝ) < x := by linarith
  set A := x ^ eps with hA
  have hA1 : 1 < A := Real.one_lt_rpow hx1 heps
  set y := x ^ ((1 : ℝ) / 52) with hy
  have hAy : A ≤ y := Real.rpow_le_rpow_of_exponent_le hx1.le heps'.le
  set q := x ^ ((1 : ℝ) / 4) with hq
  have hqy : q = y ^ (13 : ℕ) := by
    rw [hq, hy, ← Real.rpow_natCast, ← Real.rpow_mul hx0']; norm_num
  have hy1 : 1 ≤ y := by linarith
  have hy13 : y ^ 2 ≤ y ^ (13 : ℕ) := pow_le_pow_right₀ hy1 (by norm_num)
  have hq_big : C1 * A + 1 ≤ q := by
    rw [hqy]; nlinarith
  have hm : C1 * A + 1 ≤ m := le_trans hq_big h.m_lo
  have hm1 : 1 ≤ m := by nlinarith
  have hm3 : 3 ≤ m := by nlinarith
  have hm4 : m ≤ m ^ 4 := by
    calc m = m ^ 1 := (pow_one m).symm
      _ ≤ m ^ 4 := pow_le_pow_right₀ hm1 (by norm_num)
  have hf : m ≤ f := le_trans hm4 h.mf
  have hf1 : 1 ≤ f := by linarith
  have hk : m ≤ k := le_trans hf h.fk
  have hCA : C * A ≤ C1 * A := mul_le_mul_of_nonneg_right hCC1 (by linarith)
  have hB0 : 0 ≤ m ^ 5 * f * A := by positivity
  have hk1 : C1 * (m ^ 5 * f * A) ≤ k :=
    le_trans (mul_le_mul_of_nonneg_right h1 hB0) h.k_lo
  have hm25 : m ^ 2 ≤ m ^ 5 * f := by
    have : m ^ 2 ≤ m ^ 5 := pow_le_pow_right₀ hm1 (by norm_num)
    nlinarith
  have hlogk : 1 ≤ Real.log k := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hC1A : C1 ≤ C1 * A := by
    have := mul_le_mul_of_nonneg_left hA1.le (by linarith : (0:ℝ) ≤ C1)
    linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hA1⟩
  · have : C * (m ^ 5 * f * A) ≤ C1 * (m ^ 5 * f * A) := mul_le_mul_of_nonneg_right hCC1 hB0
    calc C * m ^ 5 * f * A = C * (m ^ 5 * f * A) := by ring
      _ ≤ k := le_trans this hk1
  ·
    set t := x ^ ((1 : ℝ) / 16) with ht
    have hqt : q = t ^ (4 : ℕ) := by
      rw [hq, ht, ← Real.rpow_natCast, ← Real.rpow_mul hx0']; norm_num
    have hf0 : 0 < f := by linarith
    have hlf : Real.log f ≤ 5 * Real.log x := by
      have : Real.log f ≤ Real.log (x ^ (5 : ℝ)) :=
        Real.log_le_log hf0 (le_trans h.fk h.k_hi)
      rw [Real.log_rpow (by linarith)] at this
      exact this
    have hlx : Real.log x ≤ t / (1 / 16) := Real.log_le_rpow_div hx0' (by norm_num)
    have h80 : 80 * t ≤ Real.sqrt (m / 2 - 1) := by
      rw [Real.le_sqrt (by linarith)]
      have hmq : t ^ (4 : ℕ) ≤ m := hqt ▸ h.m_lo
      have ht2 : 40000 ≤ t ^ 2 := by nlinarith
      have ht4 : t ^ (4 : ℕ) = t ^ 2 * t ^ 2 := by ring
      have : (80 * t) ^ 2 = 6400 * t ^ 2 := by ring
      nlinarith
      all_goals linarith
    have : 5 * Real.log x ≤ 80 * t := by
      have : t / (1 / 16) = 16 * t := by ring
      linarith
    linarith
  · calc C * A ≤ C1 * A := hCA
      _ ≤ m := by linarith
      _ ≤ f := hf
      _ = f * 1 := (mul_one f).symm
      _ ≤ f * Real.log k := mul_le_mul_of_nonneg_left hlogk (by linarith)
  · have hB2 : 0 ≤ m ^ 2 * A := by positivity
    calc C * (m ^ 2 * A) ≤ C1 * (m ^ 2 * A) := mul_le_mul_of_nonneg_right hCC1 hB2
      _ ≤ C1 * (m ^ 5 * f * A) := by
        apply mul_le_mul_of_nonneg_left _ (by linarith)
        exact mul_le_mul_of_nonneg_right hm25 (by linarith)
      _ ≤ k := hk1
  · linarith
  · linarith
  · linarith

end GlobalTheory.Diag.PG
