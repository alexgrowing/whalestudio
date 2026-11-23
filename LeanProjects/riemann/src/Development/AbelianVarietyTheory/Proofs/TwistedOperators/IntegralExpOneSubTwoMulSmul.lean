import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousExptPY

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory

namespace GlobalTheory.PolarU

theorem integral_one_sub_two_mul_pow (n : ℕ) :
    ∫ s in (0 : ℝ)..1, (1 - 2 * s) ^ n = (1 - (-1) ^ (n + 1)) / (2 * ((n : ℝ) + 1)) := by
  have h := intervalIntegral.integral_comp_sub_mul (a := (0 : ℝ)) (b := 1)
    (fun x : ℝ => x ^ n) (two_ne_zero' ℝ) 1
  simp only [mul_one, mul_zero, sub_zero] at h
  rw [h, integral_pow, smul_eq_mul]
  have e : (1 : ℝ) - 2 = -1 := by norm_num
  rw [e, one_pow]
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp

private theorem exp_smul_eq_tsum (A : Type) [NormedRing A] [NormedAlgebra ℝ A]
    [CompleteSpace A] (X : A) (t : ℝ) :
    NormedSpace.exp (t • X) = ∑' n : ℕ, t ^ n • (((n.factorial : ℝ)⁻¹) • X ^ n) := by
  rw [NormedSpace.exp_eq_tsum ℝ]
  refine tsum_congr fun n => ?_
  rw [smul_pow, smul_smul, smul_smul, mul_comm]

private theorem norm_one_sub_neg_one_pow_div_le_one (n : ℕ) :
    ‖(1 - (-1 : ℝ) ^ (n + 1)) / (2 * ((n : ℝ) + 1))‖ ≤ 1 := by
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [Real.norm_eq_abs, abs_le]
  rcases neg_one_pow_eq_or ℝ (n + 1) with h | h <;> rw [h]
  · norm_num
  · rw [show (1 : ℝ) - -1 = 2 by norm_num, div_mul_eq_div_div, div_self (two_ne_zero' ℝ)]
    have h0 : 0 ≤ 1 / ((n : ℝ) + 1) := by positivity
    refine ⟨by linarith, (div_le_one hn).2 ?_⟩
    have : (0 : ℝ) ≤ n := n.cast_nonneg
    linarith

theorem integral_exp_one_sub_two_mul_smul (A : Type) [NormedRing A] [NormedAlgebra ℝ A]
    [CompleteSpace A] (X : A) :
    ∫ s in (0 : ℝ)..1, NormedSpace.exp ((1 - 2 * s) • X)
      = ∑' k : ℕ, (((2 * k + 1).factorial : ℝ)⁻¹) • X ^ (2 * k) := by
  have hc : Summable fun n : ℕ => ‖((n.factorial : ℝ)⁻¹) • X ^ n‖ :=
    NormedSpace.norm_expSeries_summable' (𝕂 := ℝ) X
  simp_rw [exp_smul_eq_tsum]
  rw [intervalIntegral.integral_of_le zero_le_one]
  have hint : ∀ n : ℕ, Integrable (fun s : ℝ => (1 - 2 * s) ^ n • (((n.factorial : ℝ)⁻¹) • X ^ n))
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) := fun n =>
    (Continuous.intervalIntegrable (by fun_prop) 0 1).1
  have hbound : ∀ n : ℕ, ∫ s in Set.Ioc (0 : ℝ) 1, ‖(1 - 2 * s) ^ n • (((n.factorial : ℝ)⁻¹) • X ^ n)‖
      ≤ ‖((n.factorial : ℝ)⁻¹) • X ^ n‖ := by
    intro n
    rw [← intervalIntegral.integral_of_le zero_le_one]
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
      (C := ‖((n.factorial : ℝ)⁻¹) • X ^ n‖)
      (f := fun s : ℝ => ‖(1 - 2 * s) ^ n • (((n.factorial : ℝ)⁻¹) • X ^ n)‖) (fun s hs => by
        rw [Set.uIoc_of_le zero_le_one] at hs
        rw [norm_norm, norm_smul, norm_pow]
        refine mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) ?_)
        rw [Real.norm_eq_abs, abs_le]
        constructor <;> linarith [hs.1, hs.2])
    rw [sub_zero, abs_one, mul_one, Real.norm_eq_abs] at h
    exact (le_abs_self _).trans h
  have hsum : Summable fun n : ℕ =>
      ∫ s in Set.Ioc (0 : ℝ) 1, ‖(1 - 2 * s) ^ n • (((n.factorial : ℝ)⁻¹) • X ^ n)‖ :=
    Summable.of_nonneg_of_le (fun n => integral_nonneg fun _ => norm_nonneg _) hbound hc
  rw [← integral_tsum_of_summable_integral_norm hint hsum]
  have hterm : ∀ n : ℕ, ∫ s in Set.Ioc (0 : ℝ) 1, (1 - 2 * s) ^ n • (((n.factorial : ℝ)⁻¹) • X ^ n)
      = ((1 - (-1) ^ (n + 1)) / (2 * ((n : ℝ) + 1))) • (((n.factorial : ℝ)⁻¹) • X ^ n) := by
    intro n
    rw [← intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_smul_const,
      integral_one_sub_two_mul_pow]
  rw [tsum_congr hterm]
  set g : ℕ → A := fun n => ((1 - (-1) ^ (n + 1)) / (2 * ((n : ℝ) + 1))) •
    (((n.factorial : ℝ)⁻¹) • X ^ n) with hgdef
  have hg : Summable g := Summable.of_norm_bounded hc fun n => by
    rw [hgdef, norm_smul]
    exact mul_le_of_le_one_left (norm_nonneg _) (norm_one_sub_neg_one_pow_div_le_one n)
  have he : Summable fun k : ℕ => g (2 * k) :=
    hg.comp_injective (mul_right_injective₀ (two_ne_zero' ℕ))
  have ho : Summable fun k : ℕ => g (2 * k + 1) :=
    hg.comp_injective ((add_left_injective 1).comp (mul_right_injective₀ (two_ne_zero' ℕ)))
  rw [← tsum_even_add_odd he ho]
  have hodd : ∀ k : ℕ, g (2 * k + 1) = 0 := by
    intro k
    rw [hgdef]
    simp only
    rw [show 2 * k + 1 + 1 = 2 * (k + 1) by ring, pow_mul]
    norm_num
  have heven : ∀ k : ℕ, g (2 * k) = (((2 * k + 1).factorial : ℝ)⁻¹) • X ^ (2 * k) := by
    intro k
    rw [hgdef]
    simp only
    rw [pow_succ, pow_mul, smul_smul, Nat.factorial_succ]
    congr 1
    push_cast
    have h1 : (2 * (k : ℝ) + 1) ≠ 0 := by positivity
    have h2 : ((2 * k).factorial : ℝ) ≠ 0 := by positivity
    field_simp
    norm_num
  simp_rw [hodd, heven, tsum_zero, add_zero]

end GlobalTheory.PolarU
