import Formalism.LogVandermondeBounds.EvenOddPowerQuotientEqualityCases

namespace Formalism.LogVandermondeBounds.TaylorLogMetric

open Finset

lemma key_ineq (x : ℚ) (hx : 2 ≤ x) :
    ∀ i j : ℕ, i ≤ j → (i, j) ≠ (0, 0) →
      x ^ 3 - 2 * x ^ 2 + 3 ≤ (x ^ 2) ^ i + x * (x ^ 2) ^ j - (x ^ 2 - 1) * ((i : ℚ) + j + 1) := by
  have hq : 1 ≤ x ^ 2 := by nlinarith

  have step : ∀ i j : ℕ, (x ^ 2) ^ i + x * (x ^ 2) ^ j - (x ^ 2 - 1) * ((i : ℚ) + j + 1) ≤
      (x ^ 2) ^ i + x * (x ^ 2) ^ (j + 1) - (x ^ 2 - 1) * ((i : ℚ) + (j + 1 : ℕ) + 1) := by
    intro i j
    have hA : 1 ≤ (x ^ 2) ^ j := one_le_pow₀ hq
    have hB : 1 ≤ x * (x ^ 2) ^ j := by nlinarith
    push_cast
    rw [pow_succ (x ^ 2) j]
    have hq0 : 0 ≤ x ^ 2 - 1 := by linarith
    nlinarith [mul_le_mul_of_nonneg_right hB hq0]
  have mono : ∀ i j k : ℕ, (x ^ 2) ^ i + x * (x ^ 2) ^ j - (x ^ 2 - 1) * ((i : ℚ) + j + 1) ≤
      (x ^ 2) ^ i + x * (x ^ 2) ^ (j + k) - (x ^ 2 - 1) * ((i : ℚ) + (j + k : ℕ) + 1) := by
    intro i j k
    induction k with
    | zero => simp
    | succ k ih => exact ih.trans (by simpa [Nat.add_assoc] using step i (j + k))

  have diag : ∀ m : ℕ, x ^ 3 - 2 * x ^ 2 + 3 ≤
      (x ^ 2) ^ (m + 1) + x * (x ^ 2) ^ (m + 1) - (x ^ 2 - 1) * (((m + 1 : ℕ) : ℚ) + (m + 1 : ℕ) + 1) := by
    intro m
    induction m with
    | zero => push_cast; ring_nf; linarith
    | succ m ih =>
      have hA : 1 ≤ (x ^ 2) ^ (m + 1) := one_le_pow₀ hq
      have hB : 2 ≤ (x ^ 2) ^ (m + 1) + x * (x ^ 2) ^ (m + 1) := by nlinarith
      refine ih.trans ?_
      push_cast at *
      rw [pow_succ (x ^ 2) (m + 1)]
      nlinarith
  intro i j hij hne
  rcases Nat.eq_zero_or_pos i with rfl | hi
  ·
    have hj : 1 ≤ j := by
      rcases Nat.eq_zero_or_pos j with rfl | hj
      · exact absurd rfl hne
      · exact hj
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hj
    refine le_trans ?_ (mono 0 1 k)
    push_cast; ring_nf; linarith
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hi
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij
    have := mono (1 + m) (1 + m) k
    have h2 := diag m
    rw [Nat.add_comm 1 m] at *
    linarith

lemma sq_ge_two (p : ℕ) (hp : 2 ≤ p) : 2 ≤ p ^ 2 := by nlinarith

lemma coefL_pow (p j : ℕ) (hp : 2 ≤ p) : coefL p ((p ^ 2) ^ j) = 1 / (p : ℚ) ^ j := by
  have h : ∃ j', (p ^ 2) ^ j = (p ^ 2) ^ j' := ⟨j, rfl⟩
  unfold coefL
  rw [dif_pos h]
  have hj : j = Classical.choose h := Nat.pow_right_injective (sq_ge_two p hp) (Classical.choose_spec h)
  rw [← hj]

lemma coefL_zero (p a : ℕ) (h : ¬∃ j, a = (p ^ 2) ^ j) : coefL p a = 0 := by
  unfold coefL
  rw [dif_neg h]

lemma coefG_pow (p j : ℕ) (hp : 2 ≤ p) : coefG p (p * (p ^ 2) ^ j) = 1 / (p : ℚ) ^ (j + 1) := by
  have h : ∃ j', p * (p ^ 2) ^ j = p * (p ^ 2) ^ j' := ⟨j, rfl⟩
  unfold coefG
  rw [dif_pos h]
  have hj : j = Classical.choose h := Nat.pow_right_injective (sq_ge_two p hp)
    (Nat.eq_of_mul_eq_mul_left (by omega) (Classical.choose_spec h))
  rw [← hj]

lemma coefG_zero (p a : ℕ) (h : ¬∃ j, a = p * (p ^ 2) ^ j) : coefG p a = 0 := by
  unfold coefG
  rw [dif_neg h]

lemma coefA_pow (p i j : ℕ) (hp : 2 ≤ p) :
    coefA p ((p ^ 2) ^ i) (p * (p ^ 2) ^ j) = if i ≤ j then 1 / (p : ℚ) ^ (i + j + 1) else 0 := by
  unfold coefA
  by_cases hij : i ≤ j
  · have h : ∃ i' j', i' ≤ j' ∧ (p ^ 2) ^ i = (p ^ 2) ^ i' ∧ p * (p ^ 2) ^ j = p * (p ^ 2) ^ j' :=
      ⟨i, j, hij, rfl, rfl⟩
    rw [dif_pos h, if_pos hij]
    obtain ⟨-, h2, h3⟩ := Classical.choose_spec (Classical.choose_spec h)
    have hi : i = Classical.choose h := Nat.pow_right_injective (sq_ge_two p hp) h2
    have hj : j = Classical.choose (Classical.choose_spec h) :=
      Nat.pow_right_injective (sq_ge_two p hp) (Nat.eq_of_mul_eq_mul_left (by omega) h3)
    rw [← hj, ← hi]
  · rw [if_neg hij, dif_neg]
    rintro ⟨i', j', h1, h2, h3⟩
    have hi : i = i' := Nat.pow_right_injective (sq_ge_two p hp) h2
    have hj : j = j' := Nat.pow_right_injective (sq_ge_two p hp) (Nat.eq_of_mul_eq_mul_left (by omega) h3)
    subst hi hj
    exact hij h1

lemma coefA_zero (p a b : ℕ) (h : ¬∃ i j, i ≤ j ∧ a = (p ^ 2) ^ i ∧ b = p * (p ^ 2) ^ j) :
    coefA p a b = 0 := by
  unfold coefA
  rw [dif_neg h]

theorem logarithm_series_coefficient_identities : LogarithmSeriesIdentities := by
  intro p hp
  have hp2 : 2 ≤ p := hp.two_le
  have hp0 : 0 < p := hp.pos
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp0.ne'
  constructor
  · intro a
    by_cases hd : p ∣ a
    · obtain ⟨c, rfl⟩ := hd
      rw [if_pos (dvd_mul_right p c), Nat.mul_div_cancel_left c hp0]
      have ha1 : p * c ≠ 1 := by
        intro h
        rcases c with _ | c
        · simp at h
        · nlinarith
      rw [if_neg ha1, sub_zero]
      by_cases hc : ∃ k, c = p * (p ^ 2) ^ k
      · obtain ⟨k, rfl⟩ := hc
        rw [coefG_pow p k hp2, show p * (p * (p ^ 2) ^ k) = (p ^ 2) ^ (k + 1) by ring, coefL_pow p _ hp2]
      · rw [coefG_zero p c hc, coefL_zero]
        rintro ⟨j, hj⟩
        rcases j with _ | k
        · rw [pow_zero] at hj
          exact ha1 hj
        · apply hc
          refine ⟨k, ?_⟩
          have : p * c = p * (p * (p ^ 2) ^ k) := by rw [hj]; ring
          exact Nat.eq_of_mul_eq_mul_left hp0 this
    · rw [if_neg hd]
      by_cases ha : a = 1
      · subst ha
        have h1 := coefL_pow p 0 hp2
        rw [pow_zero, pow_zero] at h1
        rw [if_pos rfl, h1]
        norm_num
      · rw [if_neg ha, sub_zero, coefL_zero]
        rintro ⟨j, rfl⟩
        rcases j with _ | k
        · exact ha (pow_zero _)
        · exact hd (dvd_pow (dvd_pow_self p two_ne_zero) (Nat.succ_ne_zero k))
  · intro a b
    by_cases hA : ∃ i, a = p * (p ^ 2) ^ i
    · obtain ⟨i, rfl⟩ := hA
      rw [coefG_pow p i hp2]
      by_cases hB : ∃ k, b = (p ^ 2) ^ k
      · obtain ⟨k, rfl⟩ := hB
        simp only [coefB]
        rw [coefL_pow p k hp2, coefA_pow p k i hp2]
        rcases k with _ | j
        · have hn : ¬(p ∣ p * (p ^ 2) ^ i ∧ p ∣ (p ^ 2) ^ 0) := by
            rintro ⟨-, h⟩
            rw [pow_zero, Nat.dvd_one] at h
            omega
          rw [if_neg hn, if_pos (Nat.zero_le _)]
          field_simp
          ring
        · have hb : (p ^ 2) ^ (j + 1) = p * (p * (p ^ 2) ^ j) := by ring
          rw [hb, if_pos ⟨dvd_mul_right _ _, dvd_mul_right _ _⟩, Nat.mul_div_cancel_left _ hp0,
            Nat.mul_div_cancel_left _ hp0, coefA_pow p i j hp2]
          by_cases h : i ≤ j
          · rw [if_pos h, if_neg (by omega)]
            field_simp
            ring
          · rw [if_neg h, if_pos (by omega)]
            field_simp
            ring
      · simp only [coefB]
        rw [coefL_zero p b hB, coefA_zero p b _ (by rintro ⟨i', j', -, h2, -⟩; exact hB ⟨i', h2⟩)]
        simp only [mul_zero, sub_zero]
        split_ifs with h
        · obtain ⟨-, c, rfl⟩ := h
          rw [Nat.mul_div_cancel_left _ hp0, Nat.mul_div_cancel_left _ hp0]
          apply coefA_zero
          rintro ⟨i', j', -, -, h3⟩
          exact hB ⟨j' + 1, by rw [h3]; ring⟩
        · rfl
    · simp only [coefB]
      rw [coefG_zero p a hA, coefA_zero p b a (by rintro ⟨i', j', -, -, h3⟩; exact hA ⟨j', h3⟩)]
      simp only [zero_mul, zero_sub, mul_zero, neg_zero]
      split_ifs with h
      · obtain ⟨⟨c, rfl⟩, -⟩ := h
        rw [Nat.mul_div_cancel_left _ hp0]
        apply coefA_zero
        rintro ⟨i', j', -, h2, -⟩
        exact hA ⟨i', by rw [h2]⟩
      · rfl

end Formalism.LogVandermondeBounds.TaylorLogMetric
