import Mathlib
import Formalism.PeriodIntegrals.ScGapBig

namespace PI.UnitaryGroupMassFormula.ScGapBig

open PI.ScGapBig

theorem nat_bound (n m t : ℕ) (hn : 1801 ≤ n) (hm : m ≤ n + 1) (ht : t ≤ n + 6) :
    2 * (n + m * t) ^ 3 + t + 3 < 16 * n ^ 19 := by
  have hmt : m * t ≤ (n + 1) * (n + 6) := Nat.mul_le_mul hm ht
  have hsq : 1801 * n ≤ n * n := Nat.mul_le_mul_right n hn
  have h1 : n + m * t ≤ 2 * n ^ 2 := by nlinarith
  have h2 : (n + m * t) ^ 3 ≤ (2 * n ^ 2) ^ 3 := Nat.pow_le_pow_left h1 3
  have h3 : (2 * n ^ 2) ^ 3 = 8 * n ^ 6 := by ring
  have h4 : 2 ≤ n ^ 13 :=
    le_trans (by norm_num) (Nat.pow_le_pow_left (show 2 ≤ n by omega) 13)
  have h5 : n ^ 19 = n ^ 6 * n ^ 13 := by ring
  have h6 : n ^ 6 * 2 ≤ n ^ 6 * n ^ 13 := Nat.mul_le_mul_left _ h4
  have h7 : n ≤ n ^ 6 := Nat.le_self_pow (by norm_num) n
  omega

theorem scGapBig_main : ScGapBig := by
  intro k r b hn hgap
  have hrk : rk48 k r = 2 * r + k + 1 := rfl
  obtain ⟨t, hodd, ht1, ht2⟩ : ∃ t : ℕ, Odd t ∧ rk48 k r + 5 ≤ t ∧ t ≤ rk48 k r + 6 := by
    rcases Nat.even_or_odd (rk48 k r) with ⟨a, ha⟩ | ⟨a, ha⟩
    · exact ⟨rk48 k r + 5, ⟨a + 2, by omega⟩, le_refl _, by omega⟩
    · exact ⟨rk48 k r + 6, ⟨a + 3, by omega⟩, by omega, le_refl _⟩
  refine ⟨t, hodd, ht1, by omega, ?_⟩
  intro j hj
  have hm : 2 * r + 2 ≤ rk48 k r + 1 := by omega
  have hb := nat_bound (rk48 k r) (2 * r + 2) t hn hm ht2
  have hcast : 2 * ((rk48 k r + (2 * r + 2) * t : ℕ) : ℝ) ^ 3 + (t : ℝ) + 3 <
      16 * (rk48 k r : ℝ) ^ 19 := by
    exact_mod_cast hb
  linarith [hgap j hj]

end PI.UnitaryGroupMassFormula.ScGapBig
