import Mathlib

namespace UpperTheory.SmallSum

open Finset

theorem sum_log_le_of_dvd {N : ℕ} (hN : N ≠ 0) (T : Finset ℕ) (hT : ∀ l ∈ T, l.Prime ∧ l ∣ N) :
    ∑ l ∈ T, Real.log l ≤ Real.log N := by
  have hdvd : (∏ l ∈ T, l) ∣ N :=
    Finset.prod_primes_dvd N (fun l hl => (hT l hl).1.prime) (fun l hl => (hT l hl).2)
  have hpos : 0 < ∏ l ∈ T, l :=
    Nat.pos_of_ne_zero (fun h => hN (Nat.eq_zero_of_zero_dvd (h ▸ hdvd)))
  rw [← Real.log_prod (fun l hl => by exact_mod_cast (hT l hl).1.ne_zero), ← Nat.cast_prod]
  exact Real.log_le_log (by exact_mod_cast hpos)
    (by exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hN) hdvd)

theorem sum_log_small_le {Q : ℕ} (hQ : Q ≠ 0) (T : Finset ℕ) (hT : ∀ l ∈ T, l ∈ Q.primeFactors ∨ l = 3) :
    ∑ l ∈ T, Real.log l ≤ Real.log Q + 2 := by
  classical
  have hsub : T ⊆ insert 3 (T.erase 3) := by
    intro l hl
    by_cases h : l = 3
    · simp [h]
    · exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨h, hl⟩)
  have h1 : ∑ l ∈ T, Real.log l ≤ ∑ l ∈ insert 3 (T.erase 3), Real.log l :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun l _ _ => Real.log_natCast_nonneg l)
  rw [Finset.sum_insert (Finset.notMem_erase 3 T)] at h1
  have h2 : ∑ l ∈ T.erase 3, Real.log l ≤ Real.log Q := by
    apply sum_log_le_of_dvd hQ
    intro l hl
    obtain ⟨hl3, hlT⟩ := Finset.mem_erase.mp hl
    rcases hT l hlT with h | h
    · exact ⟨Nat.prime_of_mem_primeFactors h, Nat.dvd_of_mem_primeFactors h⟩
    · exact absurd h hl3
  have h3 : Real.log ((3 : ℕ) : ℝ) ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (x := ((3 : ℕ) : ℝ)) (by norm_num)
    norm_num at this ⊢
    linarith
  linarith

theorem sum_log_small_le_log {Q n : ℕ} {x C : ℝ} (hQ : Q ≠ 0) (hQn : Q ≤ n ^ 2) (hx : 0 < x) (hn : (n : ℝ) ≤ x ^ C)
    (T : Finset ℕ) (hT : ∀ l ∈ T, l ∈ Q.primeFactors ∨ l = 3) :
    ∑ l ∈ T, Real.log l ≤ 2 * C * Real.log x + 2 := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp at hQn
    exact hQ hQn
  have h1 := sum_log_small_le hQ T hT
  have h2 : Real.log Q ≤ Real.log ((n : ℝ) ^ 2) :=
    Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hQ) (by exact_mod_cast hQn)
  have h3 : Real.log (n : ℝ) ≤ C * Real.log x := by
    rw [← Real.log_rpow hx]
    exact Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hn0) hn
  rw [Real.log_pow] at h2
  push_cast at h2
  linarith

theorem sum_row_small_le {Q n : ℕ} {x C L fm b : ℝ} (hQ : Q ≠ 0) (hQn : Q ≤ n ^ 2) (hx : 1 ≤ x) (hC : 0 < C)
    (hn : (n : ℝ) ≤ x ^ C) (hL : (C + 3) ^ 2 * (1 + Real.log x) ^ 2 ≤ L) (hb : x ^ C * L ≤ b) (hfm : 1 ≤ fm)
    (T : Finset ℕ) (hT : ∀ l ∈ T, l ∈ Q.primeFactors ∨ l = 3) :
    ∑ l ∈ T, Real.log l * (C * fm * b * Real.log x + C * x ^ C * L ^ 2) ≤ 8 * C * fm * b * L ^ 2 := by
  have hy : 0 ≤ Real.log x := Real.log_nonneg hx
  have hP : 0 ≤ x ^ C := Real.rpow_nonneg (by linarith) C
  have hsum := sum_log_small_le_log hQ hQn (by linarith : (0 : ℝ) < x) hn T hT
  have hL1 : 1 ≤ L := by
    have a1 : 1 ≤ (C + 3) ^ 2 := by nlinarith
    have a2 : 1 ≤ (1 + Real.log x) ^ 2 := by nlinarith
    exact le_trans (one_le_mul_of_one_le_of_one_le a1 a2) hL
  have hL0 : 0 ≤ L := by linarith
  have hb0 : 0 ≤ b := le_trans (mul_nonneg hP hL0) hb
  have hw0 : 0 ≤ 2 * C * Real.log x + 2 := by nlinarith
  have e1 : 2 * C * Real.log x + 2 ≤ (2 * C + 2) * (1 + Real.log x) := by nlinarith
  have e2 : 2 * C + 2 ≤ (C + 3) ^ 2 := by nlinarith
  have e3 : (2 * C * Real.log x + 2) * (1 + Real.log x) ≤ L := by
    calc (2 * C * Real.log x + 2) * (1 + Real.log x)
        ≤ (2 * C + 2) * (1 + Real.log x) * (1 + Real.log x) :=
          mul_le_mul_of_nonneg_right e1 (by linarith)
      _ = (2 * C + 2) * (1 + Real.log x) ^ 2 := by ring
      _ ≤ (C + 3) ^ 2 * (1 + Real.log x) ^ 2 := mul_le_mul_of_nonneg_right e2 (sq_nonneg _)
      _ ≤ L := hL
  have hw2 : 2 * C * Real.log x + 2 ≤ L :=
    le_trans (le_mul_of_one_le_right hw0 (by linarith)) e3
  have hw1 : (2 * C * Real.log x + 2) * Real.log x ≤ L ^ 2 := by
    have : (2 * C * Real.log x + 2) * Real.log x ≤ (2 * C * Real.log x + 2) * (1 + Real.log x) :=
      mul_le_mul_of_nonneg_left (by linarith) hw0
    nlinarith
  have hCfb : 0 ≤ C * fm * b := mul_nonneg (mul_nonneg hC.le (by linarith)) hb0
  have hS : 0 ≤ C * fm * b * Real.log x + C * x ^ C * L ^ 2 :=
    add_nonneg (mul_nonneg hCfb hy) (mul_nonneg (mul_nonneg hC.le hP) (sq_nonneg _))
  have t1 : (2 * C * Real.log x + 2) * (C * fm * b * Real.log x) ≤ C * fm * b * L ^ 2 := by
    calc (2 * C * Real.log x + 2) * (C * fm * b * Real.log x)
        = (C * fm * b) * ((2 * C * Real.log x + 2) * Real.log x) := by ring
      _ ≤ (C * fm * b) * L ^ 2 := mul_le_mul_of_nonneg_left hw1 hCfb
  have t2 : (2 * C * Real.log x + 2) * (C * x ^ C * L ^ 2) ≤ C * fm * b * L ^ 2 := by
    calc (2 * C * Real.log x + 2) * (C * x ^ C * L ^ 2)
        ≤ L * (C * x ^ C * L ^ 2) :=
          mul_le_mul_of_nonneg_right hw2 (mul_nonneg (mul_nonneg hC.le hP) (sq_nonneg _))
      _ = C * L ^ 2 * (x ^ C * L) := by ring
      _ ≤ C * L ^ 2 * b := mul_le_mul_of_nonneg_left hb (mul_nonneg hC.le (sq_nonneg _))
      _ ≤ C * L ^ 2 * (b * fm) :=
          mul_le_mul_of_nonneg_left (le_mul_of_one_le_right hb0 hfm) (mul_nonneg hC.le (sq_nonneg _))
      _ = C * fm * b * L ^ 2 := by ring
  have hpos : 0 ≤ C * fm * b * L ^ 2 := mul_nonneg hCfb (sq_nonneg _)
  rw [← Finset.sum_mul]
  calc (∑ l ∈ T, Real.log l) * (C * fm * b * Real.log x + C * x ^ C * L ^ 2)
      ≤ (2 * C * Real.log x + 2) * (C * fm * b * Real.log x + C * x ^ C * L ^ 2) :=
        mul_le_mul_of_nonneg_right hsum hS
    _ = (2 * C * Real.log x + 2) * (C * fm * b * Real.log x)
        + (2 * C * Real.log x + 2) * (C * x ^ C * L ^ 2) := by ring
    _ ≤ 8 * C * fm * b * L ^ 2 := by linarith

end UpperTheory.SmallSum
