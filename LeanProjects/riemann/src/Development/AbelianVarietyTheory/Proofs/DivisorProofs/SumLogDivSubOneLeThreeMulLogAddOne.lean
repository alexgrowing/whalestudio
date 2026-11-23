import Mathlib

open Finset

namespace GlobalTheory

theorem sub_one_le_two_mul_sub_one_mul_factorization_factorial {p B : ℕ} (hp : p.Prime)
    (hpB : p ≤ B) :
    (B : ℝ) - 1 ≤ 2 * (((p : ℝ) - 1) * ((B.factorial.factorization p : ℕ) : ℝ)) := by
  have : Fact p.Prime := ⟨hp⟩
  have h1 : (p - 1) * padicValNat p B.factorial = B - (Nat.digits p B).sum :=
    sub_one_mul_padicValNat_factorial B
  have hp2 : 2 ≤ p := hp.two_le
  have hB : 0 < B := by omega
  have h2 : (Nat.digits p B).sum ≤ B % p + B / p := by
    rw [Nat.digits_def' (by omega) hB, List.sum_cons]
    exact Nat.add_le_add_left (Nat.digit_sum_le _ _) _
  have h3 : B % p + p * (B / p) = B := Nat.mod_add_div B p
  have h4 : B % p < p := Nat.mod_lt _ (by omega)
  have h5 : 1 ≤ B / p := (Nat.le_div_iff_mul_le (by omega)).2 (by omega)
  obtain ⟨m, rfl⟩ : ∃ m, p = m + 2 := ⟨p - 2, by omega⟩
  have h6 : m ≤ m * (B / (m + 2)) := Nat.le_mul_of_pos_right _ h5
  have h7 : 2 * (Nat.digits (m + 2) B).sum ≤ B + 1 := by nlinarith
  rw [Nat.factorization_def _ hp]
  have h8 : B ≤ 2 * ((m + 1) * padicValNat (m + 2) B.factorial) + 1 := by
    have : m + 2 - 1 = m + 1 := by omega
    rw [this] at h1
    omega
  have h9 : (B : ℝ) ≤ 2 * (((m : ℝ) + 1) * (padicValNat (m + 2) B.factorial : ℝ)) + 1 := by
    exact_mod_cast h8
  push_cast
  linarith

theorem factorial_succ_le_pow (n : ℕ) : (n + 1).factorial ≤ (n + 1) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.factorial_succ, pow_succ']
    exact Nat.mul_le_mul_left _ (ih.trans (Nat.pow_le_pow_left (by omega) _))

theorem sum_log_div_sub_one_le_two_mul_log {B : ℕ} (hB : 2 ≤ B) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime ∧ p ≤ B) :
    ∑ p ∈ S, Real.log p / ((p : ℝ) - 1) ≤ 2 * Real.log B := by
  have hB1 : (0 : ℝ) < (B : ℝ) - 1 := by
    have : (2 : ℝ) ≤ B := by exact_mod_cast hB
    linarith
  have h1 : ∑ p ∈ S, ((B.factorial.factorization p : ℕ) : ℝ) * Real.log p
      ≤ Real.log (B.factorial : ℕ) := by
    rw [Real.log_nat_eq_sum_factorization, Finsupp.sum]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro p hp
      rw [Nat.support_factorization, Nat.mem_primeFactors]
      exact ⟨(hS p hp).1, ((hS p hp).1.dvd_factorial).2 (hS p hp).2, B.factorial_ne_zero⟩
    · intro p _ _
      exact mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)
  have h2 : Real.log (B.factorial : ℕ) ≤ ((B : ℝ) - 1) * Real.log B := by
    obtain ⟨n, rfl⟩ : ∃ n, B = n + 1 := ⟨B - 1, by omega⟩
    have h := factorial_succ_le_pow n
    have h' : (((n + 1).factorial : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ n := by exact_mod_cast h
    have := Real.log_le_log (by exact_mod_cast (n + 1).factorial_pos) h'
    rw [Real.log_pow] at this
    convert this using 2
    push_cast; ring
  have h3 : ((B : ℝ) - 1) * ∑ p ∈ S, Real.log p / ((p : ℝ) - 1)
      ≤ 2 * ∑ p ∈ S, ((B.factorial.factorization p : ℕ) : ℝ) * Real.log p := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun p hp => ?_
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hS p hp).1.two_le
    have h := sub_one_le_two_mul_sub_one_mul_factorization_factorial (hS p hp).1 (hS p hp).2
    have hl : 0 ≤ Real.log p := Real.log_natCast_nonneg _
    rw [← mul_div_assoc, div_le_iff₀ (by linarith)]
    nlinarith [mul_le_mul_of_nonneg_right h hl]
  refine le_of_mul_le_mul_left ?_ hB1
  nlinarith

theorem log_div_sub_one_le_of_lt {B p : ℕ} (hB : 1 ≤ B) (h : B < p) :
    Real.log p / ((p : ℝ) - 1) ≤ (Real.log B + 1) / B := by
  have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hp : (B : ℝ) + 1 ≤ p := by exact_mod_cast h
  have hl : 0 ≤ Real.log B := Real.log_natCast_nonneg _
  have h1 : Real.log (p / B) ≤ p / B - 1 :=
    Real.log_le_sub_one_of_pos (div_pos (by linarith) (by linarith))
  rw [Real.log_div (by linarith) (by linarith)] at h1
  have h2 : (Real.log p - Real.log B) * B ≤ p - B := by
    have := mul_le_mul_of_nonneg_right h1 (by linarith : (0 : ℝ) ≤ B)
    rwa [sub_mul ((p : ℝ) / B), div_mul_cancel₀ _ (by linarith), one_mul] at this
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith [mul_nonneg hl (by linarith : (0 : ℝ) ≤ p - 1 - B)]

theorem sum_log_div_sub_one_le_three_mul_log_add_one :
    ∀ (B : ℕ) (S : Finset ℕ), 3 ≤ B → (∀ p ∈ S, p.Prime) →
      (S.filter (fun p => B < p)).card ≤ B →
      ∑ p ∈ S, Real.log p / ((p : ℝ) - 1) ≤ 3 * Real.log B + 1 := by
  intro B S hB hS hc
  rw [← Finset.sum_filter_add_sum_filter_not S (fun p => B < p)]
  have h1 := sum_log_div_sub_one_le_two_mul_log (B := B) (by omega)
    (S.filter (fun p => ¬ B < p)) (fun p hp => by
      rw [Finset.mem_filter] at hp
      exact ⟨hS p hp.1, by omega⟩)
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (by omega : 0 < B)
  have hl : 0 ≤ Real.log B := Real.log_natCast_nonneg _
  have h2 : ∑ p ∈ S.filter (fun p => B < p), Real.log p / ((p : ℝ) - 1)
      ≤ (S.filter (fun p => B < p)).card • ((Real.log B + 1) / B) :=
    Finset.sum_le_card_nsmul _ _ _ fun p hp =>
      log_div_sub_one_le_of_lt (by omega) (Finset.mem_filter.1 hp).2
  rw [nsmul_eq_mul] at h2
  have h3 : ((S.filter (fun p => B < p)).card : ℝ) * ((Real.log B + 1) / B)
      ≤ B * ((Real.log B + 1) / B) :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (by positivity)
  rw [mul_div_cancel₀ _ hB0.ne'] at h3
  linarith

end GlobalTheory
