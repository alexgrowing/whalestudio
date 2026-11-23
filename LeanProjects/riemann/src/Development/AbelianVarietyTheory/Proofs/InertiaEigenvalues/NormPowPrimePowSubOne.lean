import Mathlib

namespace GlobalTheory.PadicLte

theorem norm_pow_prime_sub_one (l : ℕ) [Fact l.Prime] (u : ℤ_[l])
    (h : ‖u - 1‖ < ‖((l : ℕ) : ℤ_[l])‖) :
    ‖u ^ l - 1‖ = ‖u - 1‖ * ‖((l : ℕ) : ℤ_[l])‖ := by
  have hl1 : ‖((l : ℕ) : ℤ_[l])‖ < 1 := by
    rw [PadicInt.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)
  have hpow : ∀ i : ℕ, ‖u ^ i - 1‖ ≤ ‖u - 1‖ := by
    intro i
    rw [← mul_geom_sum, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (PadicInt.norm_le_one _)
  have hsum : ∀ m : ℕ, ‖∑ i ∈ Finset.range m, (u ^ i - 1)‖ ≤ ‖u - 1‖ := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ]
      exact (PadicInt.nonarchimedean _ _).trans (max_le ih (hpow m))
  have hsplit : ∑ i ∈ Finset.range l, u ^ i
      = ((l : ℕ) : ℤ_[l]) + ∑ i ∈ Finset.range l, (u ^ i - 1) := by
    rw [Finset.sum_sub_distrib]
    simp
  have hgeom : ‖∑ i ∈ Finset.range l, u ^ i‖ = ‖((l : ℕ) : ℤ_[l])‖ := by
    rw [hsplit, PadicInt.norm_add_eq_max_of_ne]
    · exact max_eq_left ((hsum l).trans h.le)
    · exact ((hsum l).trans_lt h).ne'
  rw [← mul_geom_sum, norm_mul, hgeom]

theorem norm_pow_prime_pow_sub_one (l : ℕ) [Fact l.Prime] (u : ℤ_[l]) (k : ℕ) (hk : 2 ≤ k)
    (hu : ‖u - 1‖ = ‖((l : ℕ) : ℤ_[l])‖ ^ k) (n : ℕ) :
    ‖u ^ l ^ n - 1‖ = ‖((l : ℕ) : ℤ_[l])‖ ^ (k + n) := by
  have hl1 : ‖((l : ℕ) : ℤ_[l])‖ < 1 := by
    rw [PadicInt.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)
  have hl0 : 0 ≤ ‖((l : ℕ) : ℤ_[l])‖ := norm_nonneg _
  induction n with
  | zero => simpa using hu
  | succ n ih =>
    have hlt : ‖u ^ l ^ n - 1‖ < ‖((l : ℕ) : ℤ_[l])‖ := by
      rw [ih]
      calc ‖((l : ℕ) : ℤ_[l])‖ ^ (k + n) ≤ ‖((l : ℕ) : ℤ_[l])‖ ^ 2 :=
            pow_le_pow_of_le_one hl0 hl1.le (by omega)
        _ < ‖((l : ℕ) : ℤ_[l])‖ ^ 1 := by
            have hpos : 0 < ‖((l : ℕ) : ℤ_[l])‖ := by
              rw [PadicInt.norm_p]
              exact inv_pos.mpr (by exact_mod_cast (Fact.out : l.Prime).pos)
            exact pow_lt_pow_right_of_lt_one₀ hpos hl1 (by norm_num)
        _ = ‖((l : ℕ) : ℤ_[l])‖ := pow_one _
    rw [pow_succ, pow_mul, norm_pow_prime_sub_one l _ hlt, ih, ← pow_succ, ← add_assoc]

end GlobalTheory.PadicLte
