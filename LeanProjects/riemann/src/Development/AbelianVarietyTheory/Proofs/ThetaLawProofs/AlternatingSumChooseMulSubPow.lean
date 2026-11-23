import Mathlib

namespace GlobalTheory

open Finset

theorem fwdDiff_iter_affine_pow (g : ℕ) (a b y : ℤ) :
    (fwdDiff (1 : ℤ))^[g] (fun r : ℤ => (a * r + b) ^ g) y = g.factorial * a ^ g := by
  have hsplit : (fun r : ℤ => (a * r + b) ^ g) =
      (fun r : ℤ => ∑ k ∈ range g, (a ^ k * b ^ (g - k) * (g.choose k : ℤ)) * r ^ k) +
        a ^ g • (fun r : ℤ => r ^ g) := by
    funext r
    rw [Pi.add_apply, add_pow, sum_range_succ]
    simp only [Nat.sub_self, pow_zero, mul_one, Nat.choose_self, Nat.cast_one, Pi.smul_apply,
      smul_eq_mul]
    congr 1
    · exact sum_congr rfl fun k _ => by ring
    · ring
  have hlow : (fwdDiff (1 : ℤ))^[g]
      (fun r : ℤ => ∑ k ∈ range g, (a ^ k * b ^ (g - k) * (g.choose k : ℤ)) * r ^ k) = 0 :=
    fwdDiff_iter_sum_mul_pow_eq_zero _
  rw [hsplit, fwdDiff_iter_add, hlow, fwdDiff_iter_const_smul, fwdDiff_iter_eq_factorial]
  simp [mul_comm]

theorem alternating_sum_choose_mul_sub_pow :
    ∀ g n l : ℕ, g * n ≤ l → ∑ j ∈ Finset.range (g + 1),
      (-1 : ℤ) ^ j * (g.choose j : ℤ) * (((l - j * n) ^ g : ℕ) : ℤ)
        = (g.factorial * n ^ g : ℕ) := by
  intro g n l hgl
  have key := fwdDiff_iter_affine_pow g (-(n : ℤ)) (l : ℤ) 0
  rw [fwdDiff_iter_eq_sum_shift] at key
  simp only [smul_eq_mul, nsmul_eq_mul, zero_add, mul_one] at key
  have hterm : ∀ k ∈ range (g + 1),
      (-1 : ℤ) ^ k * (g.choose k : ℤ) * (((l - k * n) ^ g : ℕ) : ℤ) =
        (-1) ^ g * ((-1 : ℤ) ^ (g - k) * (g.choose k : ℤ) * (-(n : ℤ) * (k : ℤ) + l) ^ g) := by
    intro k hk
    have hkg : k ≤ g := Nat.lt_succ_iff.mp (mem_range.mp hk)
    have hkn : k * n ≤ l := le_trans (Nat.mul_le_mul_right n hkg) hgl
    have hsign : (-1 : ℤ) ^ k = (-1) ^ g * (-1) ^ (g - k) := by
      obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hkg
      rw [Nat.add_sub_cancel_left, pow_add, mul_assoc, ← pow_add, ← two_mul, pow_mul]
      simp
    rw [hsign, Nat.cast_pow, Nat.cast_sub hkn]
    push_cast
    ring
  rw [sum_congr rfl hterm, ← mul_sum, key]
  have hsq : (-1 : ℤ) ^ g * (-1) ^ g = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    simp
  push_cast
  rw [neg_pow]
  linear_combination ((g.factorial : ℤ) * (n : ℤ) ^ g) * hsq

end GlobalTheory
