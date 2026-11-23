import Mathlib

namespace KStar.Tree

theorem one_add_pow_prime_pow_add {T : Type} [CommRing T] {l ν k : ℕ} (hl : l.Prime) (h0 : (l : T) ^ (ν + 1) = 0) {x : T}
    (hx : x ^ l ^ k = 0) : (1 + x) ^ l ^ (k + ν) = 1 := by
  rw [add_comm, add_pow, Finset.sum_range_succ']
  have hterm : ∀ i ∈ Finset.range (l ^ (k + ν)),
      x ^ (i + 1) * 1 ^ (l ^ (k + ν) - (i + 1)) * ((l ^ (k + ν)).choose (i + 1) : T) = 0 := by
    intro i hi
    rw [one_pow, mul_one]
    by_cases hik : l ^ k ≤ i + 1
    · obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hik
      rw [hj, pow_add, hx, zero_mul, zero_mul]
    · push_neg at hik
      have hv : (i + 1).factorization l < k := by
        by_contra hc
        push_neg at hc
        have hd : l ^ k ∣ i + 1 := (hl.pow_dvd_iff_le_factorization (Nat.succ_ne_zero i)).2 hc
        exact absurd (Nat.le_of_dvd (Nat.succ_pos i) hd) (not_le.2 hik)
      have hiN : i + 1 ≤ l ^ (k + ν) := Finset.mem_range.1 hi
      have hf := Nat.factorization_choose_prime_pow hl hiN (Nat.succ_ne_zero i)
      have hdvd : l ^ (ν + 1) ∣ (l ^ (k + ν)).choose (i + 1) := by
        rw [hl.pow_dvd_iff_le_factorization (Nat.choose_pos hiN).ne', hf]
        omega
      obtain ⟨c, hc⟩ := hdvd
      rw [hc, Nat.cast_mul, Nat.cast_pow, h0, zero_mul, mul_zero]
  rw [Finset.sum_eq_zero hterm]
  simp

theorem one_add_pow_prime_pow_eq_one {T : Type} [CommRing T] {l ν M : ℕ} (hl : l.Prime) (h0 : (l : T) ^ (ν + 1) = 0)
    (hM : ν + 1 ≤ M) {x : T} (hx : x ^ l ^ (M - ν - 1) = 0) : (1 + x) ^ l ^ M = 1 := by
  have h1 := one_add_pow_prime_pow_add hl h0 hx
  have e : M = (M - ν - 1 + ν) + 1 := by omega
  rw [e, pow_succ, pow_mul, h1, one_pow]

theorem exists_eq_of_mod_eq_one {q n : ℕ} (hq : q % (2 * n) = 1) : ∃ c, q = 2 * n * c + 1 := by
  refine ⟨q / (2 * n), ?_⟩
  have h := Nat.div_add_mod q (2 * n)
  rw [hq] at h
  exact h.symm

theorem dvd_choose_two {q n : ℕ} (hq : q % (2 * n) = 1) : n ∣ q.choose 2 := by
  obtain ⟨c, rfl⟩ := exists_eq_of_mod_eq_one hq
  rw [Nat.choose_two_right, Nat.add_sub_cancel,
    show (2 * n * c + 1) * (2 * n * c) = 2 * (n * ((2 * n * c + 1) * c)) by ring,
    Nat.mul_div_cancel_left _ two_pos]
  exact dvd_mul_right _ _

theorem mod_two_mul_pow_of_le {q l k M : ℕ} (hl : l.Prime) (hk : k ≤ M) (hq : q % (2 * l ^ M) = 1) :
    q % (2 * l ^ k) = 1 := by
  have hd : 2 * l ^ k ∣ 2 * l ^ M := Nat.mul_dvd_mul_left 2 (pow_dvd_pow l hk)
  rw [← Nat.mod_mod_of_dvd q hd, hq]
  apply Nat.mod_eq_of_lt
  have h1 : 1 ≤ l ^ k := Nat.one_le_pow k l hl.pos
  omega

theorem nsmul_eq_self_of_mod {W : Type} [AddCommGroup W] {q n : ℕ} (hq : q % (2 * n) = 1) (h : ∀ m : W, n • m = 0)
    (m : W) : q • m = m := by
  obtain ⟨c, rfl⟩ := exists_eq_of_mod_eq_one hq
  rw [show 2 * n * c = n * (2 * c) by ring, add_smul, mul_smul, h, zero_add, one_smul]

end KStar.Tree
