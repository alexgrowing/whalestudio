import Mathlib

theorem UpperTheory.exists_pow_dvd_sub_of_two_pow_dvd_sub_one :
    ∀ (Q a c : ℤ) (e n : ℕ), 2 ≤ e → Odd a → Q = 1 + 2 ^ e * a → (2 : ℤ) ^ e ∣ c - 1 → ∃ i : ℕ, (2 : ℤ) ^ n ∣ Q ^ i - c := by
  intro Q a c e n he ha hQ hc
  have hL : ∀ m : ℕ, ∃ u : ℤ, Odd u ∧ Q ^ (2 ^ m) = 1 + 2 ^ (e + m) * u := by
    intro m
    induction m with
    | zero => exact ⟨a, ha, by simp [hQ]⟩
    | succ m ih =>
      obtain ⟨u, hu, hQu⟩ := ih
      obtain ⟨k, hk⟩ : ∃ k, e + m = k + 1 := ⟨e + m - 1, by omega⟩
      refine ⟨u + 2 ^ k * u ^ 2, ?_, ?_⟩
      · have hev : Even ((2 : ℤ) ^ k * u ^ 2) := by
          have hk1 : k ≠ 0 := by omega
          exact (Int.even_pow.2 ⟨even_two, hk1⟩).mul_right _
        exact hu.add_even hev
      · rw [pow_succ, pow_mul, hQu, show e + (m + 1) = k + 2 by omega, hk]
        ring
  have hQodd : Odd Q := by
    have hev : Even ((2 : ℤ) ^ e * a) :=
      (Int.even_pow.2 ⟨even_two, by omega⟩).mul_right _
    rw [hQ, add_comm]
    exact hev.add_one
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    by_cases hne : n + 1 ≤ e
    · refine ⟨0, ?_⟩
      have h1 : (2 : ℤ) ^ (n + 1) ∣ 2 ^ e := pow_dvd_pow 2 hne
      have h2 : (2 : ℤ) ^ (n + 1) ∣ c - 1 := h1.trans hc
      have h3 : Q ^ 0 - c = -(c - 1) := by ring
      rw [h3]
      exact (dvd_neg).2 h2
    · obtain ⟨i, t, ht⟩ := ih
      obtain ⟨u, hu, hQu⟩ := hL (n - e)
      rw [show e + (n - e) = n by omega] at hQu
      rcases Int.even_or_odd t with ⟨s, hs⟩ | hto
      · refine ⟨i, s, ?_⟩
        rw [ht, hs, pow_succ]
        ring
      · have hsum : Even (t + u * Q ^ i) := hto.add_odd (hu.mul (hQodd.pow))
        obtain ⟨s, hs⟩ := hsum
        refine ⟨i + 2 ^ (n - e), s, ?_⟩
        have : Q ^ (i + 2 ^ (n - e)) - c = 2 ^ n * (t + u * Q ^ i) := by
          rw [pow_add, hQu]
          linear_combination ht
        rw [this, hs, pow_succ]
        ring
