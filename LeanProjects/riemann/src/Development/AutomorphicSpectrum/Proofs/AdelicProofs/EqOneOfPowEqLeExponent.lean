import Mathlib

open MeasureTheory NumberField Matrix Filter Topology
open scoped Pointwise ENNReal

namespace GlobalTheory.CompanionTheory.Ar.Cmp

theorem eq_one_of_pow_eq_le_exponent {a n m : ℕ} (ha : a ≠ 0) (h : a ^ n = m) (hm : m ≤ n) : a = 1 := by
  by_contra h1
  have h2 : 1 < a := by omega
  have := Nat.lt_pow_self (n := n) h2
  omega

theorem ratUnit_eq_one_of_divisible :
    ∀ x : ℚˣ, (∀ n : ℕ, 0 < n → ∃ y : ℚˣ, y ^ n = x) → x = 1 := by
  intro x h
  obtain ⟨y, hy⟩ := h (2 * ((x : ℚ).num.natAbs + (x : ℚ).den + 1)) (by omega)
  set n := 2 * ((x : ℚ).num.natAbs + (x : ℚ).den + 1) with hn
  have hq : (y : ℚ) ^ n = (x : ℚ) := by rw [← hy]; simp
  have hnum : (y : ℚ).num ^ n = (x : ℚ).num := by rw [← hq, Rat.num_pow]
  have hden : (y : ℚ).den ^ n = (x : ℚ).den := by rw [← hq, Rat.den_pow]
  have h1 : (y : ℚ).den = 1 := eq_one_of_pow_eq_le_exponent (y : ℚ).den_nz hden (by omega)
  have h2 : (y : ℚ).num.natAbs = 1 :=
    eq_one_of_pow_eq_le_exponent (n := n) (m := (x : ℚ).num.natAbs)
      (Int.natAbs_ne_zero.2 (Rat.num_ne_zero.2 y.ne_zero))
      (by rw [← hnum, Int.natAbs_pow]) (by omega)
  have h3 : (y : ℚ).num ^ 2 = 1 := by
    rcases Int.natAbs_eq_iff.1 h2 with h | h <;> rw [h] <;> simp
  have h4 : (x : ℚ).num = 1 := by rw [← hnum, hn, pow_mul, h3, one_pow]
  have h5 : (x : ℚ).den = 1 := by rw [← hden, h1, one_pow]
  apply Units.ext
  rw [Units.val_one, ← Rat.num_div_den (x : ℚ), h4, h5]
  simp

end GlobalTheory.CompanionTheory.Ar.Cmp
