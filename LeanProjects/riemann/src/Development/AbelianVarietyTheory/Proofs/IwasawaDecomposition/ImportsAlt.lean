import Mathlib

namespace GlobalTheory.KeyLemmaTwo

lemma key {z : ℂ} (h : ∀ (n : ℕ), ‖z ^ n - (1 : ℂ)‖ < (1 / 2 : ℝ)) (k : ℕ) :
    (3 / 2 : ℝ) ^ k * ‖z - 1‖ ≤ ‖z ^ (2 ^ k) - 1‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    set w := z ^ (2 ^ k) with hw
    have hw2 : z ^ (2 ^ (k + 1)) = w ^ 2 := by rw [hw, ← pow_mul, pow_succ]
    have hlt : ‖w - 1‖ < 1 / 2 := h _
    have hplus : (3 / 2 : ℝ) ≤ ‖w + 1‖ := by
      have e : w + 1 = (2 : ℂ) + (w - 1) := by ring
      have h2 : ‖(2 : ℂ)‖ = 2 := by simp
      have := norm_sub_norm_le (2 : ℂ) (-(w - 1))
      rw [e]
      have h3 : ‖(2 : ℂ) - -(w - 1)‖ = ‖(2 : ℂ) + (w - 1)‖ := by rw [sub_neg_eq_add]
      rw [norm_neg, h2, h3] at this
      linarith
    have fac : w ^ 2 - 1 = (w - 1) * (w + 1) := by ring
    rw [hw2, fac, norm_mul, pow_succ]
    have hn : 0 ≤ ‖w - 1‖ := norm_nonneg _
    calc (3 / 2 : ℝ) ^ k * (3 / 2) * ‖z - 1‖ = ((3 / 2 : ℝ) ^ k * ‖z - 1‖) * (3 / 2) := by ring
      _ ≤ ‖w - 1‖ * (3 / 2) := by gcongr
      _ ≤ ‖w - 1‖ * ‖w + 1‖ := by gcongr

theorem main : ∀ {z : ℂ}, (∀ (n : ℕ), ‖z ^ n - (1 : ℂ)‖ < (1 / 2 : ℝ)) → z = (1 : ℂ) := by
  intro z h
  by_contra hne
  have hpos : 0 < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (1 / 2 / ‖z - 1‖) (by norm_num : (1 : ℝ) < 3 / 2)
  have h1 := key h k
  have h2 := h (2 ^ k)
  rw [div_lt_iff₀ hpos] at hk
  linarith

end GlobalTheory.KeyLemmaTwo
