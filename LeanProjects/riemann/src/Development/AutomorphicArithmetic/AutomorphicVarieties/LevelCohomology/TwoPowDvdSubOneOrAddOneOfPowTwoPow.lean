import Mathlib

theorem UpperTheory.two_pow_dvd_sub_one_or_add_one_of_pow_two_pow :
    ∀ (k a : ℕ) (x : ℤ), (2 : ℤ) ^ (a + k) ∣ x ^ (2 ^ k) - 1 → (2 : ℤ) ^ a ∣ x - 1 ∨ (2 : ℤ) ^ a ∣ x + 1 := by
  have B : ∀ (a : ℕ) (x : ℤ), (2 : ℤ) ^ (a + 1) ∣ x ^ 2 - 1 → (2 : ℤ) ^ a ∣ x - 1 ∨ (2 : ℤ) ^ a ∣ x + 1 := by
    intro a x h
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · left
      simp
    obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
    rcases Int.even_or_odd' x with ⟨q, hq | hq⟩
    · exfalso
      have h2 : (2 : ℤ) ∣ x ^ 2 - 1 := (dvd_pow_self 2 (by omega : b + 1 + 1 ≠ 0)).trans h
      rw [hq, show (2 * q) ^ 2 - 1 = 2 * (2 * q ^ 2) - 1 by ring] at h2
      omega
    · subst hq
      have e1 : (2 * q + 1) ^ 2 - 1 = 2 ^ 2 * (q * (q + 1)) := by ring
      rw [e1, show b + 1 + 1 = 2 + b by omega, pow_add] at h
      have h' : (2 : ℤ) ^ b ∣ q * (q + 1) := (mul_dvd_mul_iff_left (by norm_num)).1 h
      rcases Int.even_or_odd q with hqe | hqo
      · have hc : IsCoprime ((2 : ℤ) ^ b) (q + 1) :=
          (Int.isCoprime_two_left.2 hqe.add_one).pow_left
        left
        have hd := hc.dvd_of_dvd_mul_right h'
        rw [show 2 * q + 1 - 1 = 2 * q by ring, pow_succ, mul_comm ((2 : ℤ) ^ b) 2]
        exact mul_dvd_mul_left 2 hd
      · have hc : IsCoprime ((2 : ℤ) ^ b) q :=
          (Int.isCoprime_two_left.2 hqo).pow_left
        right
        have hd := hc.dvd_of_dvd_mul_left h'
        rw [show 2 * q + 1 + 1 = 2 * (q + 1) by ring, pow_succ, mul_comm ((2 : ℤ) ^ b) 2]
        exact mul_dvd_mul_left 2 hd
  intro k
  induction k with
  | zero =>
    intro a x h
    left
    simpa using h
  | succ k ih =>
    intro a x h
    have h' : (2 : ℤ) ^ ((a + 1) + k) ∣ (x ^ 2) ^ (2 ^ k) - 1 := by
      rw [← pow_mul, ← pow_succ', show a + 1 + k = a + (k + 1) by omega]
      exact h
    rcases ih (a + 1) (x ^ 2) h' with h1 | h1
    · exact B a x h1
    · rcases Nat.eq_zero_or_pos a with rfl | ha
      · left
        simp
      exfalso
      have h4 : (2 : ℤ) ^ 2 ∣ x ^ 2 + 1 := (pow_dvd_pow 2 (by omega : 2 ≤ a + 1)).trans h1
      norm_num at h4
      rcases Int.even_or_odd' x with ⟨q, hq | hq⟩
      · rw [hq, show (2 * q) ^ 2 + 1 = 4 * q ^ 2 + 1 by ring] at h4
        omega
      · rw [hq, show (2 * q + 1) ^ 2 + 1 = 4 * (q ^ 2 + q) + 2 by ring] at h4
        omega
