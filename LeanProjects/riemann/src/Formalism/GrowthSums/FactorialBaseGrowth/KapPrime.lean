import Mathlib

noncomputable section

namespace Formalism.GrowthSums

namespace KapPrime

lemma u1 {k p Y : ℝ} (hk : 1 ≤ k) (hY : 1 ≤ Y) (hp : k ^ 2 * Y ^ 2 ≤ p) : k / p ^ 2 ≤ 1 / Y := by
  have hY0 : 0 < Y := by linarith
  have hkY : 1 ≤ k * Y := one_le_mul_of_one_le_of_one_le hk hY
  have hp0 : 0 < p := lt_of_lt_of_le (by positivity) hp
  rw [div_le_div_iff₀ (by positivity) hY0]
  have h1 : k * Y ≤ (k * Y) ^ 4 := le_self_pow₀ hkY (by norm_num)
  have h2 : (k ^ 2 * Y ^ 2) ^ 2 ≤ p ^ 2 := pow_le_pow_left₀ (by positivity) hp 2
  nlinarith

lemma u2 {k p Y a b' : ℝ} (hk : 1 ≤ k) (hY : 1 ≤ Y) (hp : k ^ 2 * Y ^ 2 ≤ p) (hb0 : 0 < b')
    (hab : b' ≤ a) : k * b' / (p * a) ≤ 1 / Y := by
  have hY0 : 0 < Y := by linarith
  have hkY : 1 ≤ k * Y := one_le_mul_of_one_le_of_one_le hk hY
  have hp0 : 0 < p := lt_of_lt_of_le (by positivity) hp
  have ha0 : 0 < a := lt_of_lt_of_le hb0 hab
  rw [div_le_div_iff₀ (by positivity) hY0]
  have h1 : k * Y ≤ (k * Y) ^ 2 := le_self_pow₀ hkY (by norm_num)
  have h2 : k * Y ≤ p := by nlinarith
  calc k * b' * Y = (k * Y) * b' := by ring
    _ ≤ p * a := mul_le_mul h2 hab hb0.le hp0.le
    _ = 1 * (p * a) := by ring

lemma u3 {k p Y La N₁ : ℝ} (hk : 1 ≤ k) (hY : 1 ≤ Y) (hN₁ : 1 ≤ N₁) (hp : k ^ 2 * Y ^ 2 ≤ p)
    (_hLa0 : 0 ≤ La) (hLa : La < k) : La * N₁ / p ≤ N₁ / Y := by
  have hY0 : 0 < Y := by linarith
  have hkY : 1 ≤ k * Y := one_le_mul_of_one_le_of_one_le hk hY
  have hp0 : 0 < p := lt_of_lt_of_le (by positivity) hp
  rw [div_le_div_iff₀ hp0 hY0]
  have h1 : k * Y ≤ (k * Y) ^ 2 := le_self_pow₀ hkY (by norm_num)
  have h2 : La * Y ≤ p := by nlinarith
  have hN₁0 : 0 ≤ N₁ := by linarith
  calc La * N₁ * Y = N₁ * (La * Y) := by ring
    _ ≤ N₁ * p := mul_le_mul_of_nonneg_left h2 hN₁0

lemma u4 {k Y Yb N La la a b' : ℝ} (hk : 1 ≤ k) (hY : 1 ≤ Y) (hYb : 1 ≤ Yb) (hN : 1 ≤ N)
    (hla : 1 ≤ la) (hLa : 1 ≤ La) (hb0 : 0 < b') (ha : k * Y ^ 2 * Yb * N * La * la * b' ≤ a) :
    La * b' / a ≤ 1 / Y := by
  have hY0 : 0 < Y := by linarith
  have hm : 1 ≤ k * Y * Yb * N * la :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hk hY) hYb) hN) hla
  have hLa0 : 0 < La := by linarith
  have hLb : 0 ≤ La * b' * Y := by positivity
  have h1 : La * b' * Y * 1 ≤ La * b' * Y * (k * Y * Yb * N * la) :=
    mul_le_mul_of_nonneg_left hm hLb
  have ha0 : 0 < a := by
    have : 0 < k * Y ^ 2 * Yb * N * La * la * b' := by
      have : 0 < k := by linarith
      have : 0 < Yb := by linarith
      have : 0 < N := by linarith
      have : 0 < la := by linarith
      positivity
    linarith
  rw [div_le_div_iff₀ ha0 hY0]
  have h2 : La * b' * Y * (k * Y * Yb * N * la) = k * Y ^ 2 * Yb * N * La * la * b' := by ring
  linarith

lemma u5 {Cc k N N₁ Q c a Y Z : ℝ} (hk : 1 ≤ k) (hN : 1 ≤ N) (hN₁ : 1 ≤ N₁) (hQ : 1 ≤ Q)
    (hY : 1 ≤ Y) (hZ : 1 ≤ Z) (hc0 : 0 ≤ c) (hc : c ≤ 2 * Cc * Z)
    (ha : k ^ 3 * N * Q ^ 4 * Z * Y ≤ a) :
    k ^ 3 * N₁ * Q ^ 2 * c / a ≤ 2 * Cc * N₁ / (N * Y) := by
  have hk0 : 0 < k := by linarith
  have hQ0 : 0 < Q := by linarith
  have hN0 : 0 < N := by linarith
  have hY0 : 0 < Y := by linarith
  have hZ0 : 0 < Z := by linarith
  have hN₁0 : 0 < N₁ := by linarith
  have hW : 0 < k ^ 3 * N * Q ^ 4 * Z * Y := by positivity
  have ha0 : 0 < a := lt_of_lt_of_le hW ha
  have hCc : 0 ≤ Cc := by nlinarith
  have hQ2 : Q ^ 2 ≤ Q ^ 4 := pow_le_pow_right₀ hQ (by norm_num)
  rw [div_le_div_iff₀ ha0 (by positivity)]
  calc k ^ 3 * N₁ * Q ^ 2 * c * (N * Y) ≤ k ^ 3 * N₁ * Q ^ 2 * (2 * Cc * Z) * (N * Y) := by gcongr
    _ = 2 * Cc * N₁ * (k ^ 3 * N * Q ^ 2 * Z * Y) := by ring
    _ ≤ 2 * Cc * N₁ * (k ^ 3 * N * Q ^ 4 * Z * Y) := by gcongr
    _ ≤ 2 * Cc * N₁ * a := by gcongr

end KapPrime

end Formalism.GrowthSums
