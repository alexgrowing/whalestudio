import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations

namespace GlobalTheory.Cyc

theorem geom_sum_one_add_expand {R : Type*} [CommRing R] (y : R) (n : ℕ) :
    ∃ z : R, (1 + y) ^ n - 1 = y * ((n : R) + (n.choose 2 : ℕ) * y + y ^ 2 * z) := by
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨z, hz⟩ := ih
    refine ⟨z + (n.choose 2 : ℕ) + y * z, ?_⟩
    have h : (1 + y) ^ n = 1 + y * ((n : R) + (n.choose 2 : ℕ) * y + y ^ 2 * z) := by
      rw [← hz]; ring
    have hc : (n + 1).choose 2 = n + n.choose 2 := by
      rw [Nat.choose_succ_succ' n 1, Nat.choose_one_right]
    rw [pow_succ, h, hc]
    push_cast
    ring

variable {l : ℕ} [hl : Fact l.Prime]

theorem padicInt_norm_add_eq_of_lt {a b : ℤ_[l]} (h : ‖b‖ < ‖a‖) : ‖a + b‖ = ‖a‖ := by
  rw [PadicInt.norm_add_eq_max_of_ne h.ne', max_eq_left h.le]

theorem norm_pow_sub_one_of_not_dvd (x : ℤ_[l]) (hx : ‖x - 1‖ < 1) (n : ℕ) (hn : ¬ l ∣ n) :
    ‖x ^ n - 1‖ = ‖x - 1‖ := by
  obtain ⟨z, hz⟩ := geom_sum_one_add_expand (x - 1) n
  rw [add_sub_cancel] at hz
  have hn1 : ‖(n : ℤ_[l])‖ = 1 := by
    apply le_antisymm (PadicInt.norm_le_one _)
    by_contra h
    push_neg at h
    have h' : ‖((n : ℤ) : ℤ_[l])‖ < 1 := by simpa using h
    rw [PadicInt.norm_int_lt_one_iff_dvd] at h'
    exact hn (Int.natCast_dvd_natCast.mp h')
  have e : (n : ℤ_[l]) + (n.choose 2 : ℕ) * (x - 1) + (x - 1) ^ 2 * z
      = n + (x - 1) * ((n.choose 2 : ℕ) + (x - 1) * z) := by ring
  rw [hz, norm_mul, e, padicInt_norm_add_eq_of_lt, hn1, mul_one]
  rw [hn1, norm_mul]
  exact lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) (PadicInt.norm_le_one _)) hx

theorem norm_pow_prime_sub_one (x : ℤ_[l]) (hx : ‖x - 1‖ ≤ (l : ℝ)⁻¹)
    (h2 : l = 2 → ‖x - 1‖ < (l : ℝ)⁻¹) :
    ‖x ^ l - 1‖ = ‖x - 1‖ * ‖(l : ℤ_[l])‖ := by
  obtain ⟨z, hz⟩ := geom_sum_one_add_expand (x - 1) l
  rw [add_sub_cancel] at hz
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.out.one_lt
  have hi0 : (0 : ℝ) < (l : ℝ)⁻¹ := by positivity
  have hi1 : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl1
  have hsq : (l : ℝ)⁻¹ * (l : ℝ)⁻¹ < (l : ℝ)⁻¹ := mul_lt_of_lt_one_right hi0 hi1
  have hA : ‖((l.choose 2 : ℕ) : ℤ_[l]) * (x - 1)‖ < (l : ℝ)⁻¹ := by
    rw [norm_mul]
    by_cases h : l = 2
    · exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) (PadicInt.norm_le_one _)) (h2 h)
    · have hlt : 2 < l := lt_of_le_of_ne hl.out.two_le (Ne.symm h)
      obtain ⟨c, hc⟩ := hl.out.dvd_choose_self (k := 2) (by norm_num) hlt
      have : ‖((l.choose 2 : ℕ) : ℤ_[l])‖ ≤ (l : ℝ)⁻¹ := by
        rw [hc, Nat.cast_mul, norm_mul, PadicInt.norm_p]
        exact mul_le_of_le_one_right hi0.le (PadicInt.norm_le_one _)
      exact lt_of_le_of_lt (mul_le_mul this hx (norm_nonneg _) hi0.le) hsq
  have hB : ‖(x - 1) ^ 2 * z‖ < (l : ℝ)⁻¹ := by
    rw [norm_mul, sq, norm_mul]
    refine lt_of_le_of_lt (mul_le_of_le_one_right (by positivity) (PadicInt.norm_le_one _)) ?_
    exact lt_of_le_of_lt (mul_le_mul hx hx (norm_nonneg _) hi0.le) hsq
  rw [hz, norm_mul, add_assoc, padicInt_norm_add_eq_of_lt]
  rw [PadicInt.norm_p]
  exact lt_of_le_of_lt (PadicInt.nonarchimedean _ _) (max_lt hA hB)

theorem norm_pow_nat_sub_one (n : ℕ) (hn : n ≠ 0) : ∀ (x : ℤ_[l]), ‖x - 1‖ ≤ (l : ℝ)⁻¹ →
    (l = 2 → ‖x - 1‖ < (l : ℝ)⁻¹) → ‖x ^ n - 1‖ = ‖x - 1‖ * ‖(n : ℤ_[l])‖ := by
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.out.one_lt
  have hi1 : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl1
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro x hx h2
    by_cases hd : l ∣ n
    · obtain ⟨m, rfl⟩ := hd
      have hm : m ≠ 0 := by rintro rfl; simp at hn
      have hlt : m < l * m := lt_mul_of_one_lt_left (Nat.pos_of_ne_zero hm) hl.out.one_lt
      have key := norm_pow_prime_sub_one x hx h2
      have hle : ‖x ^ l - 1‖ ≤ ‖x - 1‖ := by
        rw [key]; exact mul_le_of_le_one_right (norm_nonneg _) (PadicInt.norm_le_one _)
      rw [pow_mul, ih m hlt hm (x ^ l) (hle.trans hx) (fun h => hle.trans_lt (h2 h)), key,
        Nat.cast_mul, norm_mul, mul_assoc]
    · have hn1 : ‖(n : ℤ_[l])‖ = 1 := by
        apply le_antisymm (PadicInt.norm_le_one _)
        by_contra h
        push_neg at h
        have h' : ‖((n : ℤ) : ℤ_[l])‖ < 1 := by simpa using h
        rw [PadicInt.norm_int_lt_one_iff_dvd] at h'
        exact hd (Int.natCast_dvd_natCast.mp h')
      rw [norm_pow_sub_one_of_not_dvd x (hx.trans_lt hi1) n hd, hn1, mul_one]

theorem norm_unit_zpow_sub_one :
    ∀ (l : ℕ) [Fact l.Prime], ∀ (s : ℕ) (u : ℤ_[l]ˣ), 1 ≤ s → (l = 2 → 2 ≤ s) →
      ‖(u : ℤ_[l]) - 1‖ = (l : ℝ) ^ (-(s : ℤ)) → ∀ n : ℤ, n ≠ 0 →
      ‖((u ^ n : ℤ_[l]ˣ) : ℤ_[l]) - 1‖ = (l : ℝ) ^ (-(s : ℤ)) * ‖(n : ℤ_[l])‖ := by
  intro l hl s u hs h2 hu n hn
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.out.one_lt
  have hx : ‖(u : ℤ_[l]) - 1‖ ≤ (l : ℝ)⁻¹ := by
    rw [hu, ← zpow_neg_one]
    exact zpow_le_zpow_right₀ hl1.le (by omega)
  have hx2 : l = 2 → ‖(u : ℤ_[l]) - 1‖ < (l : ℝ)⁻¹ := fun h => by
    have := h2 h
    rw [hu, ← zpow_neg_one]
    exact zpow_lt_zpow_right₀ hl1 (by omega)
  obtain ⟨m, rfl | rfl⟩ := n.eq_nat_or_neg
  · have hm : m ≠ 0 := by rintro rfl; simp at hn
    rw [zpow_natCast, Units.val_pow_eq_pow_val, norm_pow_nat_sub_one m hm _ hx hx2, hu,
      Int.cast_natCast]
  · have hm : m ≠ 0 := by rintro rfl; simp at hn
    have e : (((u ^ m)⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) - 1
        = -((((u ^ m)⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) * (((u ^ m : ℤ_[l]ˣ) : ℤ_[l]) - 1)) := by
      rw [mul_sub, Units.inv_mul]; ring
    rw [zpow_neg, zpow_natCast, e, norm_neg, norm_mul, PadicInt.norm_units, one_mul,
      Units.val_pow_eq_pow_val, norm_pow_nat_sub_one m hm _ hx hx2, hu, Int.cast_neg, norm_neg,
      Int.cast_natCast]

end GlobalTheory.Cyc
