import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.Imports
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff

open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam

namespace GlobalTheory.ThZero

lemma ee_add (a b : ℂ) : ee (a + b) = ee a * ee b := by
  simp only [ee, mul_add, Complex.exp_add]

lemma ee_ne (a : ℂ) : ee a ≠ 0 := Complex.exp_ne_zero _

lemma ee_neg (a : ℂ) : ee (-a) = (ee a)⁻¹ := by
  simp only [ee, mul_neg, Complex.exp_neg]

lemma ee_pow (a : ℂ) (n : ℕ) : ee a ^ n = ee ((n : ℂ) * a) := by
  simp only [ee]
  rw [← Complex.exp_nat_mul]
  congr 1
  ring

lemma ee_eq_one_iff (a : ℂ) : ee a = 1 ↔ ∃ k : ℤ, a = k := by
  have h : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := Complex.two_pi_I_ne_zero
  simp only [ee, Complex.exp_eq_one_iff]
  refine exists_congr fun k => ⟨fun hk => ?_, fun hk => ?_⟩
  · apply mul_left_cancel₀ h
    rw [hk]; ring
  · rw [hk]; ring

lemma norm_ee_lt_one (τ : ℍ) : ‖ee (τ : ℂ)‖ < 1 := by
  simp only [ee, Complex.norm_exp]
  rw [Real.exp_lt_one_iff]
  have h1 := τ.im_pos
  have h2 := Real.pi_pos
  have : (2 * (Real.pi : ℂ) * Complex.I * (τ : ℂ)).re = -(2 * Real.pi * τ.im) := by
    simp
  rw [this]
  have : 0 < 2 * Real.pi * τ.im := by positivity
  linarith

lemma summable_nine_pow_mul_inv_sq_succ (τ : ℍ) (c : ℂ) : Summable fun n : ℕ => ‖-(ee (τ : ℂ) ^ (n + 1) * c)‖ := by
  have h := summable_geometric_of_lt_one (norm_nonneg _) (norm_ee_lt_one τ)
  refine (h.mul_right (‖ee (τ : ℂ)‖ * ‖c‖)).congr fun n => ?_
  simp only [norm_neg, norm_mul, norm_pow, pow_succ]
  ring

lemma tprod_ne (τ : ℍ) (a b : ℂ) (ha : ∀ n : ℕ, 1 - ee (τ : ℂ) ^ (n + 1) * a ≠ 0)
    (hb : ∀ n : ℕ, 1 - ee (τ : ℂ) ^ (n + 1) * b ≠ 0) :
    ∏' n : ℕ, (1 - ee (τ : ℂ) ^ (n + 1) * a) * (1 - ee (τ : ℂ) ^ (n + 1) * b) ≠ 0 := by
  simp only [sub_eq_add_neg] at ha hb ⊢
  rw [(multipliable_one_add_of_summable (summable_nine_pow_mul_inv_sq_succ τ a)).tprod_mul
    (multipliable_one_add_of_summable (summable_nine_pow_mul_inv_sq_succ τ b))]
  exact mul_ne_zero (tprod_one_add_ne_zero_of_summable ha (summable_nine_pow_mul_inv_sq_succ τ a))
    (tprod_one_add_ne_zero_of_summable hb (summable_nine_pow_mul_inv_sq_succ τ b))

lemma first_iff (z : ℂ) : ee (z / 2) - ee (-z / 2) = 0 ↔ ∃ k : ℤ, z = k := by
  rw [← ee_eq_one_iff, sub_eq_zero]
  have h1 : ee z = ee (z / 2) * ee (z / 2) := by rw [← ee_add]; congr 1; ring
  have h2 : ee (-z / 2) = (ee (z / 2))⁻¹ := by rw [← ee_neg]; congr 1; ring
  rw [h1, h2]
  have h3 := ee_ne (z / 2)
  constructor
  · intro h
    nth_rewrite 2 [h]
    exact mul_inv_cancel₀ h3
  · intro h
    exact eq_inv_of_mul_eq_one_left h

lemma fac_iff (τ : ℍ) (w : ℂ) (n : ℕ) :
    1 - ee (τ : ℂ) ^ (n + 1) * ee w = 0 ↔ ∃ k : ℤ, ((n : ℂ) + 1) * τ + w = k := by
  rw [ee_pow, ← ee_add, sub_eq_zero, eq_comm, ee_eq_one_iff]
  push_cast
  rfl

theorem th_eq_zero_iff :
    ∀ (τ : ℍ) (z : ℂ), th z τ = 0 ↔ ∃ m n : ℤ, z = (m : ℂ) * (τ : ℂ) + n := by
  intro τ z
  unfold th
  constructor
  · intro h
    by_contra hne
    refine (mul_ne_zero (mul_ne_zero (ee_ne _) ?_) (tprod_ne τ _ _ ?_ ?_)) h
    · rw [Ne, first_iff]
      rintro ⟨k, hk⟩
      exact hne ⟨0, k, by simp [hk]⟩
    · intro n
      rw [Ne, fac_iff]
      rintro ⟨k, hk⟩
      exact hne ⟨-((n : ℤ) + 1), k, by push_cast; linear_combination hk⟩
    · intro n
      rw [← ee_neg, Ne, fac_iff]
      rintro ⟨k, hk⟩
      exact hne ⟨(n : ℤ) + 1, -k, by push_cast; linear_combination -hk⟩
  · rintro ⟨m, k, hz⟩
    rcases lt_trichotomy m 0 with hm | hm | hm
    · obtain ⟨n, rfl⟩ : ∃ n : ℕ, m = -((n : ℤ) + 1) := ⟨(-m - 1).toNat, by omega⟩
      have : 1 - ee (τ : ℂ) ^ (n + 1) * ee z = 0 :=
        (fac_iff τ z n).2 ⟨k, by rw [hz]; push_cast; ring⟩
      rw [tprod_of_exists_eq_zero ⟨n, by rw [this, zero_mul]⟩, mul_zero]
    · have : ee (z / 2) - ee (-z / 2) = 0 := (first_iff z).2 ⟨k, by simp [hz, hm]⟩
      rw [this, mul_zero, zero_mul]
    · obtain ⟨n, rfl⟩ : ∃ n : ℕ, m = (n : ℤ) + 1 := ⟨(m - 1).toNat, by omega⟩
      have : 1 - ee (τ : ℂ) ^ (n + 1) * (ee z)⁻¹ = 0 := by
        rw [← ee_neg]
        exact (fac_iff τ (-z) n).2 ⟨-k, by rw [hz]; push_cast; ring⟩
      rw [tprod_of_exists_eq_zero ⟨n, by rw [this, mul_zero]⟩, mul_zero]

end GlobalTheory.ThZero
