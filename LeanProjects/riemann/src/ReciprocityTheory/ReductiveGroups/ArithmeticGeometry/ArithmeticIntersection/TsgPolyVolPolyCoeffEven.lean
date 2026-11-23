import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.APrime

namespace ReciprocityTheory.ChartRestriction.G.AI

open Polynomial

private theorem neg_X_pow_eq_C_neg_one_pow_mul_X_pow (j : ℕ) : ((-X : ℝ[X]) ^ j) = C ((-1 : ℝ) ^ j) * X ^ j := by
  have hX : (-X : ℝ[X]) = C (-1) * X := by
    ext n
    rw [Polynomial.coeff_neg, Polynomial.coeff_C_mul]
    ring
  rw [hX, mul_pow, ← map_pow]

theorem volPoly_coeff (D : ℕ) (J : ℕ → ℝ) (n : ℕ) :
    (volPoly D J).coeff n = (D.choose n : ℝ) * J n * (-1) ^ n := by
  have h : ∀ j, (C ((D.choose j : ℝ) * J j) * (-X) ^ j : ℝ[X]) =
      C ((D.choose j : ℝ) * J j * (-1) ^ j) * X ^ j := by
    intro j
    rw [neg_X_pow_eq_C_neg_one_pow_mul_X_pow, ← mul_assoc, ← map_mul]
  rw [volPoly, Finset.sum_congr rfl fun j _ => h j, Polynomial.finset_sum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  split_ifs with hn
  · rfl
  · rw [Nat.choose_eq_zero_of_lt (by simp at hn; omega)]
    simp

theorem tsgPoly_coeff_zero (D : ℕ) (κ : ℕ → ℝ) (P : ℝ[X]) : (tsgPoly D κ P).coeff 0 = 0 := by
  rw [tsgPoly, Polynomial.finset_sum_coeff]
  refine Finset.sum_eq_zero fun n _ => ?_
  split_ifs <;> simp [Polynomial.coeff_C_mul_X_pow]

theorem tsgPoly_coeff_succ (D : ℕ) (κ : ℕ → ℝ) (P : ℝ[X]) (m : ℕ) :
    (tsgPoly D κ P).coeff (m + 1) =
      if Odd m then ((D : ℝ) + 1) * κ ((m + 1) / 2) / (((m + 1) / 2 : ℕ) : ℝ) * P.coeff m else 0 := by
  rw [tsgPoly, Polynomial.finset_sum_coeff, Finset.sum_eq_single m]
  · by_cases ho : Odd m
    · rw [if_pos ho, if_pos ho, Polynomial.coeff_C_mul_X_pow, if_pos rfl]
    · rw [if_neg ho, if_neg ho, Polynomial.coeff_zero]
  · intro n _ hnm
    by_cases ho : Odd n
    · rw [if_pos ho, Polynomial.coeff_C_mul_X_pow, if_neg (by omega)]
    · rw [if_neg ho, Polynomial.coeff_zero]
  · intro hm
    have h0 : P.coeff m = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (by simp at hm; omega)
    by_cases ho : Odd m
    · rw [if_pos ho, Polynomial.coeff_C_mul_X_pow, if_pos rfl, h0, mul_zero]
    · rw [if_neg ho, Polynomial.coeff_zero]

noncomputable def FibreSquare.evenPoly {D : ℕ} (S : FibreSquare D) : ℝ[X] :=
  ∑ j ∈ Finset.range (D + 1 + 1),
    C (((D + 1).choose j : ℝ) * ((-1) ^ j + 1) * S.I (mix j S.ξ S.A)) * X ^ j

theorem tsgPoly_volPoly_coeff_even (D : ℕ) (J κ : ℕ → ℝ) (k : ℕ) (hk : 1 ≤ k) :
    (tsgPoly D κ (volPoly D J)).coeff (2 * k) =
      -(2 * ((D + 1).choose (2 * k) : ℝ) * (κ k * J (2 * k - 1))) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have h2 : 2 * (j + 1) = 2 * j + 1 + 1 := by ring
  have h3 : (2 * j + 1 + 1) / 2 = j + 1 := by omega
  have hodd : Odd (2 * j + 1) := ⟨j, rfl⟩
  rw [h2, tsgPoly_coeff_succ, if_pos hodd, volPoly_coeff, h3, Nat.add_sub_cancel,
    Odd.neg_one_pow hodd]
  have hc : (D + 1) * D.choose (2 * j + 1) = (D + 1).choose (2 * j + 1 + 1) * (2 * j + 1 + 1) := by
    first
    | exact Nat.add_one_mul_choose_eq D (2 * j + 1)
    | exact Nat.succ_mul_choose_eq D (2 * j + 1)
  have hc' : ((D : ℝ) + 1) * (D.choose (2 * j + 1) : ℝ) =
      ((D + 1).choose (2 * j + 1 + 1) : ℝ) * (2 * j + 1 + 1) := by exact_mod_cast hc
  have hj : ((j + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  push_cast at hj ⊢
  field_simp
  first
  | linear_combination (κ (j + 1) * J (2 * j + 1)) * hc'
  | linear_combination (-(κ (j + 1) * J (2 * j + 1))) * hc'
  | linear_combination (2 * κ (j + 1) * J (2 * j + 1)) * hc'
  | linear_combination (-(2 * κ (j + 1) * J (2 * j + 1))) * hc'

theorem tsgPoly_coeff_odd (D : ℕ) (κ : ℕ → ℝ) (P : ℝ[X]) (k : ℕ) :
    (tsgPoly D κ P).coeff (2 * k + 1) = 0 := by
  rw [tsgPoly_coeff_succ, if_neg (Nat.not_odd_iff_even.2 (even_two_mul k))]

end ReciprocityTheory.ChartRestriction.G.AI
