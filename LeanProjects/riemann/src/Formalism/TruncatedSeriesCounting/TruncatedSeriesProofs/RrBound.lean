import Formalism.TruncatedSeriesCounting.AprimeArith

noncomputable section

namespace Formalism.TruncatedSeriesCounting.WachCoordinates

open Finset

private theorem geom_sum_range_mul_one_sub (x : ℝ) :
    ∀ n : ℕ, Finset.sum (range n) (fun i => x ^ i) * (1 - x) = 1 - x ^ n := fun
  | 0 => by simp
  | n + 1 => by rw [sum_range_succ, add_mul, geom_sum_range_mul_one_sub x n, pow_succ]; ring

theorem tsum_le_two_level (x A B D : ℝ) (j : ℕ) (f : ℕ → ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1)
    (hA0 : 0 ≤ A) (hf0 : ∀ a, 0 ≤ f a) (hfB : ∀ a, f a ≤ (B + D) * x ^ a)
    (hfA : ∀ a, a < j → f a ≤ (A + D) * x ^ a) :
    ∑' a, f a ≤ (A + B * x ^ j + D) * (1 - x)⁻¹ := by
  have hx1' : 0 < 1 - x := by linarith
  have hgeo : Summable (fun a : ℕ => (B + D) * x ^ a) :=
    (summable_geometric_of_lt_one hx0 hx1).mul_left (B + D)
  have hsum : Summable f := Summable.of_nonneg_of_le hf0 hfB hgeo
  have hsplit : Finset.sum (range j) f + ∑' a, f (a + j) = ∑' a, f a := by
    exact hsum.sum_add_tsum_nat_add j
  have hshift : Summable (fun a => f (a + j)) := by
    exact (summable_nat_add_iff j).mpr hsum
  have hg2 : HasSum (fun a : ℕ => (B + D) * x ^ j * x ^ a) ((B + D) * x ^ j * (1 - x)⁻¹) :=
    (hasSum_geometric_of_lt_one hx0 hx1).mul_left _
  have h2 : ∑' a, f (a + j) ≤ (B + D) * x ^ j * (1 - x)⁻¹ :=
    hasSum_le (fun a => by
      calc f (a + j) ≤ (B + D) * x ^ (a + j) := hfB (a + j)
        _ = (B + D) * x ^ j * x ^ a := by rw [pow_add]; ring) hshift.hasSum hg2
  have h1 : Finset.sum (range j) f ≤ (A + D) * Finset.sum (range j) (fun a => x ^ a) := by
    rw [mul_sum]
    exact sum_le_sum fun a ha => hfA a (mem_range.mp ha)
  have hS' : Finset.sum (range j) (fun a => x ^ a) = (1 - x ^ j) * (1 - x)⁻¹ := by
    rw [← geom_sum_range_mul_one_sub x j, mul_assoc, mul_inv_cancel₀ hx1'.ne', mul_one]
  have hpos : 0 ≤ A * x ^ j * (1 - x)⁻¹ :=
    mul_nonneg (mul_nonneg hA0 (pow_nonneg hx0 _)) (inv_nonneg.mpr hx1'.le)
  rw [← hsplit]
  calc Finset.sum (range j) f + ∑' a, f (a + j)
      ≤ (A + D) * Finset.sum (range j) (fun a => x ^ a) + (B + D) * x ^ j * (1 - x)⁻¹ :=
        add_le_add h1 h2
    _ = (A + B * x ^ j + D) * (1 - x)⁻¹ - A * x ^ j * (1 - x)⁻¹ := by rw [hS']; ring
    _ ≤ (A + B * x ^ j + D) * (1 - x)⁻¹ := by linarith

theorem rr_arith (l d G h y C L s r q : ℝ) (hld : l = d + 1) (hd2 : 2 ≤ d) (hG0 : 0 ≤ G)
    (hh0 : 0 ≤ h) (hy0 : 0 ≤ y) (hC0 : 0 ≤ C) (hCL : C ≤ 3 + L) (hL0 : 0 ≤ L)
    (hq : q = d / (d - 1)) (hsA : s ≤ (2 * G + 2 * h * y + C + 3) * q)
    (hr : r ≤ s * l / d ^ 2 + C) : r ≤ 20 * (G / l + h * y / d + L + 1) := by
  subst hld
  subst hq
  have hd1 : 0 < d - 1 := by linarith
  have hd0 : 0 < d := by linarith
  have hl0 : 0 < d + 1 := by linarith
  have hdd : 0 < (d - 1) * d := mul_pos hd1 hd0
  have hst : s * (d + 1) / d ^ 2 ≤ (2 * G + 2 * h * y + C + 3) * ((d + 1) / ((d - 1) * d)) := by
    have h1 : s * (d + 1) / d ^ 2 ≤ (2 * G + 2 * h * y + C + 3) * (d / (d - 1)) * (d + 1) / d ^ 2 := by
      have e : (2 * G + 2 * h * y + C + 3) * (d / (d - 1)) * (d + 1) / d ^ 2 - s * (d + 1) / d ^ 2
          = ((2 * G + 2 * h * y + C + 3) * (d / (d - 1)) - s) * ((d + 1) / d ^ 2) := by ring
      have : 0 ≤ ((2 * G + 2 * h * y + C + 3) * (d / (d - 1)) - s) * ((d + 1) / d ^ 2) :=
        mul_nonneg (by linarith) (div_nonneg hl0.le (sq_nonneg d))
      linarith
    have h2 : (2 * G + 2 * h * y + C + 3) * (d / (d - 1)) * (d + 1) / d ^ 2
        = (2 * G + 2 * h * y + C + 3) * ((d + 1) / ((d - 1) * d)) := by
      have hd1' : d - 1 ≠ 0 := hd1.ne'
      have hd0' : d ≠ 0 := hd0.ne'
      field_simp
    linarith
  have ht0 : 0 ≤ (d + 1) / ((d - 1) * d) := div_nonneg hl0.le hdd.le
  have htc : (d + 1) / ((d - 1) * d) ≤ 3 / 2 := by
    have key : d + 1 ≤ 3 / 2 * ((d - 1) * d) := by
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ d - 2) (by linarith : (0:ℝ) ≤ 3 * d + 1)]
    exact (div_le_iff₀ hdd).mpr key
  have htG : (d + 1) / ((d - 1) * d) ≤ 10 / (d + 1) := by
    have key : (d + 1) * (d + 1) ≤ 10 * ((d - 1) * d) := by
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ d - 2) (by linarith : (0:ℝ) ≤ 9 * d + 6)]
    exact (div_le_div_iff₀ hdd hl0).mpr key
  have hth : (d + 1) / ((d - 1) * d) ≤ 3 / d := by
    have key : (d + 1) * d ≤ 3 * ((d - 1) * d) := by
      nlinarith [mul_nonneg hd0.le (by linarith : (0:ℝ) ≤ d - 2)]
    exact (div_le_div_iff₀ hdd hd0).mpr key
  have e1 : 2 * G * ((d + 1) / ((d - 1) * d)) ≤ 20 * (G / (d + 1)) := by
    calc 2 * G * ((d + 1) / ((d - 1) * d)) ≤ 2 * G * (10 / (d + 1)) :=
          mul_le_mul_of_nonneg_left htG (by linarith)
      _ = 20 * (G / (d + 1)) := by ring
  have hhy : 0 ≤ h * y := mul_nonneg hh0 hy0
  have e2 : 2 * h * y * ((d + 1) / ((d - 1) * d)) ≤ 20 * (h * y / d) := by
    have hq0 : 0 ≤ h * y / d := div_nonneg hhy hd0.le
    calc 2 * h * y * ((d + 1) / ((d - 1) * d)) = 2 * (h * y) * ((d + 1) / ((d - 1) * d)) := by ring
      _ ≤ 2 * (h * y) * (3 / d) := mul_le_mul_of_nonneg_left hth (by linarith)
      _ = 6 * (h * y / d) := by ring
      _ ≤ 20 * (h * y / d) := by linarith
  have e3 : (C + 3) * ((d + 1) / ((d - 1) * d)) ≤ (C + 3) * (3 / 2) :=
    mul_le_mul_of_nonneg_left htc (by linarith)
  have expand : (2 * G + 2 * h * y + C + 3) * ((d + 1) / ((d - 1) * d)) + C
      = 2 * G * ((d + 1) / ((d - 1) * d)) + 2 * h * y * ((d + 1) / ((d - 1) * d))
        + (C + 3) * ((d + 1) / ((d - 1) * d)) + C := by ring
  linarith

theorem remainder_bound_of_tsum : RrBound := by
  intro ℓ hℓ n _ H G h j cut s r hh hH hG hs hr
  have hL3 : (3:ℝ) ≤ (ℓ:ℝ) := by exact_mod_cast hℓ
  have hb : (1:ℝ) < (ℓ:ℝ) := by linarith
  have hh1 : (1:ℝ) ≤ (h:ℝ) := by exact_mod_cast hh
  have hlog0 : 0 ≤ Real.logb ℓ (2 * h + 1) := Real.logb_nonneg hb (by linarith)
  have hceil := Nat.ceil_lt_add_one (R := ℝ) (a := 1 + Real.logb ℓ (2 * h + 1)) (by linarith)
  have hlog3 : Real.logb ℓ 3 ≤ 1 := by
    rw [← Real.logb_self_eq_one hb]
    exact (Real.logb_le_logb hb (by norm_num) (by linarith)).mpr hL3
  have hlogmul : Real.logb ℓ (2 * h + 1) ≤ Real.logb ℓ 3 + Real.logb ℓ h := by
    rw [← Real.logb_mul (by norm_num) (by linarith)]
    exact (Real.logb_le_logb hb (by linarith) (by nlinarith)).mpr (by linarith)
  have hL0 : 0 ≤ Real.logb ℓ h := Real.logb_nonneg hb hh1
  have hC0 : (0:ℝ) ≤ (⌈1 + Real.logb ℓ (2 * h + 1)⌉₊ : ℝ) := Nat.cast_nonneg _
  have hCL : (⌈1 + Real.logb ℓ (2 * h + 1)⌉₊ : ℝ) ≤ 3 + Real.logb ℓ h := by linarith
  have hd2 : (2:ℝ) ≤ (ℓ:ℝ) - 1 := by linarith
  have hdpos : (0:ℝ) < (ℓ:ℝ) - 1 := by linarith
  have hx0 : (0:ℝ) ≤ 1 / ((ℓ:ℝ) - 1) := by positivity
  have hx1 : 1 / ((ℓ:ℝ) - 1) < 1 := by rw [div_lt_one hdpos]; linarith
  have hser := tsum_le_two_level (1 / ((ℓ:ℝ) - 1)) (2 * G) (2 * h)
    ((⌈1 + Real.logb ℓ (2 * h + 1)⌉₊ : ℝ) + 3) j
    (fun a : ℕ => ((H (cut + ((a + 1 : ℕ) : ZMod n)) : ℝ) +
        (⌈1 + Real.logb ℓ (2 * h + 1)⌉₊ : ℝ) + 3) / ((ℓ : ℝ) - 1) ^ a)
    hx0 hx1 (by positivity) (fun a => by positivity)
    (fun a => by
      have h' : ((H (cut + ((a + 1 : ℕ) : ZMod n)) : ℝ)) ≤ 2 * h := by
        exact_mod_cast hH (cut + ((a + 1 : ℕ) : ZMod n))
      rw [one_div, inv_pow, ← div_eq_mul_inv]
      exact div_le_div_of_nonneg_right (by linarith) (pow_nonneg hdpos.le a))
    (fun a ha => by
      have h' : ((H (cut + ((a + 1 : ℕ) : ZMod n)) : ℝ)) ≤ 2 * G := by
        exact_mod_cast hG (a + 1) (by omega) (by omega)
      rw [one_div, inv_pow, ← div_eq_mul_inv]
      exact div_le_div_of_nonneg_right (by linarith) (pow_nonneg hdpos.le a))
  have hsA := hs.trans hser
  have hq : (1 - 1 / ((ℓ:ℝ) - 1))⁻¹ = ((ℓ:ℝ) - 1) / ((ℓ:ℝ) - 1 - 1) := by
    have hd0 : (ℓ:ℝ) - 1 ≠ 0 := by linarith
    have hd1 : (ℓ:ℝ) - 1 - 1 ≠ 0 := by linarith
    field_simp
  have hyd : (h:ℝ) / ((ℓ:ℝ) - 1) ^ (j + 1) =
      (h:ℝ) * (1 / ((ℓ:ℝ) - 1)) ^ j / ((ℓ:ℝ) - 1) := by
    have hd0 : (ℓ:ℝ) - 1 ≠ 0 := by linarith
    rw [pow_succ, one_div_pow]
    field_simp
  rw [hyd]
  have key := rr_arith (ℓ:ℝ) ((ℓ:ℝ) - 1) (G:ℝ) (h:ℝ) ((1 / ((ℓ:ℝ) - 1)) ^ j)
    (⌈1 + Real.logb ℓ (2 * h + 1)⌉₊ : ℝ) (Real.logb ℓ h) s r
    (1 - 1 / ((ℓ:ℝ) - 1))⁻¹ (by ring) hd2 (Nat.cast_nonneg _) (by linarith)
    (pow_nonneg hx0 j) hC0 hCL hL0 hq (by linarith) hr
  exact key

end Formalism.TruncatedSeriesCounting.WachCoordinates
