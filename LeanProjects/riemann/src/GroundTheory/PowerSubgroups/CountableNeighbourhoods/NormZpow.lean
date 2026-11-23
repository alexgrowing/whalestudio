import Mathlib

namespace GroundTheory.Variant₂.N1

theorem eq_one_of_forall_norm_zpow_sub_one_lt {z : ℂ} (h : ∀ m : ℤ, ‖z ^ m - 1‖ < 1) :
    z = 1 := by
  have hpow : ∀ n : ℕ, ‖z ^ n - 1‖ < 1 := fun n => by simpa using h n
  have hle : ‖z‖ ≤ 1 := by
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (2 : ℝ) hlt
    have h1 := hpow n
    have h2 : ‖z ^ n‖ - ‖(1 : ℂ)‖ ≤ ‖z ^ n - 1‖ := norm_sub_norm_le _ _
    rw [norm_pow, norm_one] at h2
    linarith
  have hz0 : z ≠ 0 := by
    rintro rfl
    have := hpow 1
    simp at this
  have hge : 1 ≤ ‖z‖ := by
    by_contra hlt
    rw [not_le] at hlt
    have hpos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
    have h1 : 1 < ‖z⁻¹‖ := by
      rw [norm_inv]
      exact (one_lt_inv₀ hpos).mpr hlt
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (2 : ℝ) h1
    have h3 := h (-(n : ℤ))
    rw [zpow_neg, zpow_natCast, ← inv_pow] at h3
    have h2 : ‖z⁻¹ ^ n‖ - ‖(1 : ℂ)‖ ≤ ‖z⁻¹ ^ n - 1‖ := norm_sub_norm_le _ _
    rw [norm_pow, norm_one] at h2
    linarith
  have hn1 : ‖z‖ = 1 := le_antisymm hle hge
  have key : ∀ w : ℂ, ‖w‖ = 1 → ‖w - 1‖ < 1 → 3 * ‖w - 1‖ ^ 2 ≤ ‖w ^ 2 - 1‖ ^ 2 := by
    intro w hw hw1
    have e : w ^ 2 - 1 = (w - 1) * (w + 1) := by ring
    rw [e, norm_mul, mul_pow]
    have hw' : w.re ^ 2 + w.im ^ 2 = 1 := by
      have := Complex.sq_norm w
      rw [hw, Complex.normSq_apply] at this
      nlinarith
    have a1 : ‖w - 1‖ ^ 2 = (w.re - 1) ^ 2 + w.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp
      ring
    have a2 : ‖w + 1‖ ^ 2 = (w.re + 1) ^ 2 + w.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp
      ring
    have a3 : 3 ≤ ‖w + 1‖ ^ 2 := by
      have : ‖w - 1‖ ^ 2 < 1 := by nlinarith [norm_nonneg (w - 1)]
      nlinarith
    nlinarith [sq_nonneg ‖w - 1‖]
  have hk : ∀ k : ℕ, 3 ^ k * ‖z - 1‖ ^ 2 ≤ ‖z ^ (2 ^ k) - 1‖ ^ 2 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have h4 := key (z ^ (2 ^ k)) (by rw [norm_pow, hn1, one_pow]) (hpow _)
      rw [pow_succ 2 k, pow_mul]
      calc (3 : ℝ) ^ (k + 1) * ‖z - 1‖ ^ 2 = 3 * (3 ^ k * ‖z - 1‖ ^ 2) := by ring
        _ ≤ 3 * ‖z ^ (2 ^ k) - 1‖ ^ 2 := by gcongr
        _ ≤ _ := h4
  by_contra hne
  have hd : 0 < ‖z - 1‖ ^ 2 := pow_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hne)) 2
  obtain ⟨k, hk'⟩ := pow_unbounded_of_one_lt (1 / ‖z - 1‖ ^ 2) (by norm_num : (1 : ℝ) < 3)
  have h5 := hk k
  have h6 := hpow (2 ^ k)
  have h7 : ‖z ^ (2 ^ k) - 1‖ ^ 2 < 1 := by nlinarith [norm_nonneg (z ^ (2 ^ k) - 1)]
  have h8 : 1 < 3 ^ k * ‖z - 1‖ ^ 2 := by rwa [div_lt_iff₀ hd] at hk'
  linarith

end GroundTheory.Variant₂.N1
