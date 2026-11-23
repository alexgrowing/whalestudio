import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.StripEstimates.FaceMapCompSuccAboveCastSucc
open Ad3 Ad3.S

namespace GlobalTheory.CompanionTheory.HeckeSq

theorem norm_char_prime {N : ℕ} (χ : DirichletCharacter ℂ N) {p : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N) :
    ‖χ (p : ZMod N)‖ = 1 := by
  haveI : NeZero N := ⟨by rintro rfl; exact hpN (dvd_zero p)⟩
  obtain ⟨u, hu⟩ := (ZMod.isUnit_iff_coprime p N).2 ((Nat.Prime.coprime_iff_not_dvd hp).2 hpN)
  rw [← hu]
  exact DirichletCharacter.unit_norm_eq_one χ u

theorem norm_prime_sq_pow {k N : ℕ} {χ : DirichletCharacter ℂ N} {a : ℕ → ℂ} {p : ℕ} (hp : p.Prime)
    (hpN : ¬ p ∣ N) {α β : ℂ} (hm : α * β = χ p * (p : ℂ) ^ (k - 1)) (hn : ‖α‖ = ‖β‖)
    (hpow : ∀ j, a (p ^ j) = ∑ i ∈ Finset.range (j + 1), α ^ i * β ^ (j - i)) (j : ℕ) :
    ‖a (p ^ (2 * j))‖ ≤ ((2 * j + 1 : ℕ) : ℝ) * ((p ^ j : ℕ) : ℝ) ^ (k - 1) := by
  have hsq : ‖α‖ ^ 2 = (p : ℝ) ^ (k - 1) := by
    have h := congrArg norm hm
    rw [norm_mul, norm_mul, norm_char_prime χ hp hpN, one_mul, norm_pow, Complex.norm_natCast, ← hn] at h
    rw [sq]; exact h
  rw [hpow]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ i ∈ Finset.range (2 * j + 1),
      ‖α ^ i * β ^ (2 * j - i)‖ = ((p ^ j : ℕ) : ℝ) ^ (k - 1) := by
    intro i hi
    have hi' : i ≤ 2 * j := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    rw [norm_mul, norm_pow, norm_pow, ← hn, ← pow_add, Nat.add_sub_cancel' hi', pow_mul, hsq]
    push_cast
    rw [← pow_mul, ← pow_mul, mul_comm]
  rw [Finset.sum_congr rfl hterm]
  simp

theorem card_divisors_prime_sq {p : ℕ} (hp : p.Prime) (j : ℕ) :
    ((p ^ j) ^ 2).divisors.card = 2 * j + 1 := by
  rw [← pow_mul, mul_comm j 2, Nat.divisors_prime_pow hp]
  simp

theorem norm_sq_le : ∀ (k N : ℕ) (χ : DirichletCharacter ℂ N) (a : ℕ → ℂ), IsEig k N χ a → E2a →
    (∀ p : ℕ, p.Prime → ¬ p ∣ N → ∃ α β : ℂ, α + β = a p ∧ α * β = χ p * (p : ℂ) ^ (k - 1) ∧ ‖α‖ = ‖β‖) →
    ∀ n : ℕ, Nat.Coprime n N → ‖a (n ^ 2)‖ ≤ (((n ^ 2).divisors.card : ℕ) : ℝ) * (n : ℝ) ^ (k - 1) := by
  intro k N χ a he hE hS n
  obtain ⟨hmul, hpp⟩ := hE k N χ a he
  obtain ⟨h0, h1, -⟩ := he
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p j hp hj =>
    intro hc
    have hpN : ¬ p ∣ N := fun hd =>
      hp.one_lt.ne' (Nat.eq_one_of_dvd_coprimes hc (dvd_pow_self p hj.ne') hd)
    obtain ⟨α, β, hs, hm, hn⟩ := hS p hp hpN
    have hb := norm_prime_sq_pow hp hpN hm hn (hpp p hp α β hs hm) j
    rw [card_divisors_prime_sq hp j, ← pow_mul, mul_comm j 2]
    exact hb
  | zero =>
    intro _
    simp [h0]
  | one =>
    intro _
    simp [h1]
  | coprime m n hm hn hmn ihm ihn =>
    intro hc
    have hcm : Nat.Coprime m N := Nat.Coprime.coprime_mul_right hc
    have hcn : Nat.Coprime n N := Nat.Coprime.coprime_mul_left hc
    have hsq : Nat.Coprime (m ^ 2) (n ^ 2) := Nat.Coprime.pow 2 2 hmn
    rw [mul_pow, hmul _ _ hsq, norm_mul, hsq.card_divisors_mul]
    push_cast
    rw [mul_pow]
    calc ‖a (m ^ 2)‖ * ‖a (n ^ 2)‖
        ≤ (((m ^ 2).divisors.card : ℝ) * (m : ℝ) ^ (k - 1)) *
            (((n ^ 2).divisors.card : ℝ) * (n : ℝ) ^ (k - 1)) :=
          mul_le_mul (ihm hcm) (ihn hcn) (norm_nonneg _) (le_trans (norm_nonneg _) (ihm hcm))
      _ = _ := by ring

end GlobalTheory.CompanionTheory.HeckeSq
