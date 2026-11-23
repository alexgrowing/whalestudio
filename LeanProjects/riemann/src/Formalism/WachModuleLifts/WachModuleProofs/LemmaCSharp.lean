import Formalism.WachModuleLifts.Statement

open Finset

noncomputable section

namespace Formalism.CL

namespace CSharp

variable {p : ℕ} [hp : Fact p.Prime]

def Zp (p : ℕ) [Fact p.Prime] : Polynomial ℚ_[p] :=
  Polynomial.C ((p : ℚ_[p])⁻¹) * Polynomial.X ^ (p - 1) *
    (Polynomial.X + Polynomial.C (-(p : ℚ_[p])))

lemma Zp_pow (n : ℕ) : Zp p ^ n = Polynomial.C ((p : ℚ_[p])⁻¹ ^ n) *
    (Polynomial.X ^ ((p - 1) * n) * (Polynomial.X + Polynomial.C (-(p : ℚ_[p]))) ^ n) := by
  simp only [Zp, mul_pow, Polynomial.C_pow, ← pow_mul]
  ring

lemma coeff_Zp_pow (n m : ℕ) : (Zp p ^ n).coeff m =
    if (p - 1) * n ≤ m then (p : ℚ_[p])⁻¹ ^ n *
      ((-(p : ℚ_[p])) ^ (n - (m - (p - 1) * n)) * (n.choose (m - (p - 1) * n) : ℚ_[p]))
    else 0 := by
  rw [Zp_pow, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_mul']
  split_ifs
  · rw [Polynomial.coeff_X_add_C_pow]
  · rw [mul_zero]

lemma norm_natCast_le_one' (m : ℕ) : ‖(m : ℚ_[p])‖ ≤ 1 := by
  simpa using Padic.norm_int_le_one (p := p) (m : ℤ)

lemma norm_coeff_Zp_pow_le (n m : ℕ) (h : (p - 1) * n ≤ m) :
    ‖(Zp p ^ n).coeff m‖ ≤ (p : ℝ) ^ (m - (p - 1) * n) := by
  rw [coeff_Zp_pow, if_pos h]
  set i := m - (p - 1) * n with hi
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.1.pos
  by_cases hin : i ≤ n
  · rw [norm_mul, norm_mul, norm_pow, norm_pow, norm_inv, norm_neg, Padic.norm_p, inv_inv]
    have hsplit : (p : ℝ) ^ n = (p : ℝ) ^ i * (p : ℝ) ^ (n - i) := by
      rw [← pow_add, Nat.add_sub_cancel' hin]
    have hc := norm_natCast_le_one' (p := p) (n.choose i)
    rw [hsplit, inv_pow]
    have hpi : (0 : ℝ) < (p : ℝ) ^ (n - i) := pow_pos hp0 _
    calc (p : ℝ) ^ i * (p : ℝ) ^ (n - i) * (((p : ℝ) ^ (n - i))⁻¹ * ‖(n.choose i : ℚ_[p])‖)
        = (p : ℝ) ^ i * ‖(n.choose i : ℚ_[p])‖ := by field_simp
      _ ≤ (p : ℝ) ^ i * 1 := by gcongr
      _ = (p : ℝ) ^ i := mul_one _
  · rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, mul_zero, mul_zero, norm_zero]
    positivity

lemma coeff_Zp_pow_lt (r n : ℕ) (hn : n < r) : (Zp p ^ n).coeff (p * r) = 0 := by
  rw [coeff_Zp_pow]
  split_ifs with h
  · have h1 : p * n < p * r := Nat.mul_lt_mul_of_pos_left hn hp.1.pos
    have h2 : (p - 1) * n + n = p * n := by
      rw [Nat.sub_mul, one_mul, Nat.sub_add_cancel (Nat.le_mul_of_pos_left n hp.1.pos)]
    rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, mul_zero, mul_zero]
  · rfl

lemma coeff_Zp_pow_self (r : ℕ) : (Zp p ^ r).coeff (p * r) = (p : ℚ_[p])⁻¹ ^ r := by
  have h2 : (p - 1) * r + r = p * r := by
    rw [Nat.sub_mul, one_mul, Nat.sub_add_cancel (Nat.le_mul_of_pos_left r hp.1.pos)]
  rw [coeff_Zp_pow, if_pos (by omega)]
  have h3 : p * r - (p - 1) * r = r := by omega
  rw [h3, Nat.sub_self, pow_zero, Nat.choose_self, Nat.cast_one, mul_one, mul_one]

lemma norm_coeff_Zp_pow_gt (r n : ℕ) (hn : r < n) :
    ‖(Zp p ^ n).coeff (p * r)‖ ≤ (p : ℝ) ^ ((r : ℤ) - ((p - 1 : ℕ) : ℤ)) := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.1.one_le
  by_cases h : (p - 1) * n ≤ p * r
  · refine (norm_coeff_Zp_pow_le n (p * r) h).trans ?_
    rw [← zpow_natCast]
    apply zpow_le_zpow_right₀ hp1
    have h2 : (p - 1) * r + r = p * r := by
      rw [Nat.sub_mul, one_mul, Nat.sub_add_cancel (Nat.le_mul_of_pos_left r hp.1.pos)]
    have h3 : (p - 1) * (r + 1) ≤ (p - 1) * n := Nat.mul_le_mul_left _ hn
    rw [Nat.mul_add, mul_one] at h3
    push_cast [h]
    omega
  · rw [coeff_Zp_pow, if_neg h, norm_zero]
    positivity

lemma core (r : ℕ) (s : Finset ℕ) (hr : r ∈ s) (a : ℕ → ℚ_[p]) (ha : ∀ n, ‖a n‖ ≤ 1)
    (v : ℕ) (hv : v < p - 1) (har : ‖a r‖ = (p : ℝ) ^ (-(v : ℤ))) :
    ‖∑ n ∈ s, (Zp p ^ n).coeff (p * r) * a n‖ = (p : ℝ) ^ ((r : ℤ) - v) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.1.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.1.one_lt
  rw [← Finset.add_sum_erase s _ hr]
  have hmain : ‖(Zp p ^ r).coeff (p * r) * a r‖ = (p : ℝ) ^ ((r : ℤ) - v) := by
    rw [coeff_Zp_pow_self, norm_mul, har, norm_pow, norm_inv, Padic.norm_p, inv_inv,
      ← zpow_natCast, ← zpow_add₀ hp0.ne']
    congr 1
  have hrest : ‖∑ n ∈ s.erase r, (Zp p ^ n).coeff (p * r) * a n‖ ≤
      (p : ℝ) ^ ((r : ℤ) - ((p - 1 : ℕ) : ℤ)) := by
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
    intro n hn
    have hnr : n ≠ r := Finset.ne_of_mem_erase hn
    rw [norm_mul]
    rcases lt_or_gt_of_ne hnr with hlt | hgt
    · rw [coeff_Zp_pow_lt r n hlt, norm_zero, zero_mul]
      positivity
    · calc ‖(Zp p ^ n).coeff (p * r)‖ * ‖a n‖ ≤ ‖(Zp p ^ n).coeff (p * r)‖ * 1 := by
            gcongr; exact ha n
        _ ≤ _ := by rw [mul_one]; exact norm_coeff_Zp_pow_gt r n hgt
  have hlt : (p : ℝ) ^ ((r : ℤ) - ((p - 1 : ℕ) : ℤ)) < (p : ℝ) ^ ((r : ℤ) - v) :=
    zpow_lt_zpow_right₀ hp1 (by omega)
  have hne : ‖(Zp p ^ r).coeff (p * r) * a r‖ ≠
      ‖∑ n ∈ s.erase r, (Zp p ^ n).coeff (p * r) * a n‖ := by
    rw [hmain]; exact (lt_of_le_of_lt hrest hlt).ne'
  rw [Padic.add_eq_max_of_ne hne, hmain]
  exact max_eq_left (hrest.trans hlt.le)

end CSharp

end Formalism.CL
