import Mathlib

namespace GlobalTheory

theorem _root_.GlobalTheory.bar_gap_param_ineq : ∀ (T D c0 h0 N f m k PP : ℝ), 4 * D + 4 ≤ T → 4 * T ^ 2 ≤ h0 → PP * T * N * f ^ 2 * m ^ 2 * k * D ≤ h0 →
    4 * (c0 + 2 * N + T + D + 1) ≤ h0 → 0 ≤ c0 → c0 ≤ 22 * f ^ 2 * N ^ 4 → D = f * (N * (N - 1) / 2) → 40 ≤ PP →
    N + 4 ≤ 2 * k → 2 ≤ m → 6 ≤ N → 8 ≤ f →
    (T + c0) * (T + D + 1) + c0 + 2 * N - 2 ≤ h0 ∧ 2 * N + D ≤ T := by
  intro T D c0 h0 N f m k PP hTD hT2 hP h4 hc0 hc0u hD hPP hk hm hN hf
  have hNN : 5 * N ≤ N * (N - 1) := by nlinarith
  have hD1 : 4 * (N * (N - 1)) ≤ D := by
    rw [hD]; nlinarith [mul_nonneg (sub_nonneg.2 hf) (by nlinarith : (0:ℝ) ≤ N * (N - 1))]
  have hD0 : 0 ≤ D := by nlinarith
  have hgap : 2 * N + D ≤ T := by nlinarith
  refine ⟨?_, hgap⟩
  have hT0 : 0 ≤ T := by linarith
  have hm2 : 4 ≤ m ^ 2 := by nlinarith
  have hk0 : 0 ≤ k := by linarith
  have hA : 160 ≤ PP * m ^ 2 := by nlinarith [mul_nonneg (sub_nonneg.2 hPP) (sq_nonneg m)]
  have hB : 80 * N ≤ PP * m ^ 2 * k := by
    nlinarith [mul_nonneg (sub_nonneg.2 hA) hk0]
  have hC : 320 * (N ^ 2 * (N - 1)) ≤ PP * m ^ 2 * k * D := by
    nlinarith [mul_nonneg (sub_nonneg.2 hB) hD0, mul_nonneg (by linarith : (0:ℝ) ≤ 80 * N) (sub_nonneg.2 hD1)]
  have hE : 264 * N ^ 3 ≤ PP * m ^ 2 * k * D := by
    nlinarith [mul_nonneg (sq_nonneg N) (by linarith : (0:ℝ) ≤ 56 * N - 320)]
  have hX : 0 ≤ T * N * f ^ 2 := by
    have : 0 ≤ N := by linarith
    positivity
  have hF : 264 * N ^ 3 * (T * N * f ^ 2) ≤ PP * T * N * f ^ 2 * m ^ 2 * k * D := by
    have := mul_le_mul_of_nonneg_right hE hX
    calc 264 * N ^ 3 * (T * N * f ^ 2) ≤ PP * m ^ 2 * k * D * (T * N * f ^ 2) := this
      _ = PP * T * N * f ^ 2 * m ^ 2 * k * D := by ring
  have hcT : 12 * (c0 * T) ≤ h0 := by
    have h1 : c0 * T ≤ 22 * f ^ 2 * N ^ 4 * T := mul_le_mul_of_nonneg_right hc0u hT0
    nlinarith
  have hcD : c0 * (4 * (D + 1)) ≤ c0 * T := mul_le_mul_of_nonneg_left (by linarith) hc0
  have hTT : T * (4 * (D + 1)) ≤ T * T := mul_le_mul_of_nonneg_left (by linarith) hT0
  have hexp : (T + c0) * (T + D + 1) + c0 + 2 * N - 2
      = T ^ 2 + T * (D + 1) + c0 * T + c0 * (D + 1) + c0 + 2 * N - 2 := by ring
  rw [hexp]
  nlinarith

end GlobalTheory
