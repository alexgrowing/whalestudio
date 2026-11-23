import Mathlib

namespace GlobalTheory.CompanionTheory.DivisorCount

private lemma two_mul_add_one_le_three_pow (k : ℕ) : 2 * k + 1 ≤ 3 ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ]; omega

private lemma two_mul_add_one_le_two_mul_two_pow (k : ℕ) : 2 * k + 1 ≤ 2 * 2 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    rw [pow_succ]; omega

private lemma card_divisors_sq_prime_pow {p k : ℕ} (hp : p.Prime) :
    (((p ^ k) ^ 2).divisors).card = 2 * k + 1 := by
  rw [← pow_mul, Nat.divisors_prime_pow hp, Finset.card_map, Finset.card_range]
  ring

theorem card_divisors_sq_le_strong (n : ℕ) :
    (n ^ 2).divisors.card ≤ 2 * n ∧ (Odd n → (n ^ 2).divisors.card ≤ n) := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp hk =>
    rw [card_divisors_sq_prime_pow hp]
    rcases hp.eq_two_or_odd' with rfl | hodd
    · refine ⟨?_, fun h => ?_⟩
      · exact two_mul_add_one_le_two_mul_two_pow k
      · exact absurd h (by
          rw [Nat.not_odd_iff_even]
          exact (Nat.even_pow.mpr ⟨even_two, hk.ne'⟩))
    · have h3 : 3 ≤ p := by
        have := hp.two_le
        rcases hodd with ⟨m, rfl⟩
        omega
      have h : 2 * k + 1 ≤ p ^ k :=
        (two_mul_add_one_le_three_pow k).trans (Nat.pow_le_pow_left h3 k)
      exact ⟨by omega, fun _ => h⟩
  | zero => simp
  | one => simp
  | coprime a b ha hb hab iha ihb =>
    have hcop : Nat.Coprime (a ^ 2) (b ^ 2) := Nat.Coprime.pow 2 2 hab
    have hcard : ((a * b) ^ 2).divisors.card
        = (a ^ 2).divisors.card * (b ^ 2).divisors.card := by
      rw [mul_pow, hcop.card_divisors_mul]
    rw [hcard]
    have hodd : Odd a ∨ Odd b := by
      by_contra h
      rw [not_or] at h
      have h1 : Even a := Nat.not_odd_iff_even.mp h.1
      have h2 : Even b := Nat.not_odd_iff_even.mp h.2
      have : 2 ∣ Nat.gcd a b := Nat.dvd_gcd h1.two_dvd h2.two_dvd
      rw [hab] at this
      omega
    constructor
    · rcases hodd with h | h
      · calc _ ≤ a * (2 * b) := Nat.mul_le_mul (iha.2 h) ihb.1
          _ = 2 * (a * b) := by ring
      · calc _ ≤ (2 * a) * b := Nat.mul_le_mul iha.1 (ihb.2 h)
          _ = 2 * (a * b) := by ring
    · intro h
      obtain ⟨h1, h2⟩ := Nat.odd_mul.mp h
      exact Nat.mul_le_mul (iha.2 h1) (ihb.2 h2)

theorem card_divisors_sq_le_two_mul (n : ℕ) :
    (((n ^ 2).divisors.card : ℕ) : ℝ) ≤ 2 * n := by
  exact_mod_cast (card_divisors_sq_le_strong n).1

end GlobalTheory.CompanionTheory.DivisorCount
