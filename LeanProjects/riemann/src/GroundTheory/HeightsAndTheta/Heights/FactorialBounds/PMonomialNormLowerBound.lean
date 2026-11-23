import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FactorialBounds.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Finset

theorem MonomialNormLowerBound.factorial_le_prod_mul_pow (i : ℕ) (a : Fin i → ℕ) :
    (∑ j, a j).factorial ≤ (∏ j, (a j).factorial) * i ^ (∑ j, a j) := by
  have hsum := Finset.sum_pow_eq_sum_piAntidiag (univ : Finset (Fin i)) (fun _ => (1 : ℕ))
    (∑ j, a j)
  simp only [one_pow, prod_const_one, mul_one, sum_const, card_univ, Fintype.card_fin,
    smul_eq_mul] at hsum
  have hmem : a ∈ piAntidiag (univ : Finset (Fin i)) (∑ j, a j) := by
    rw [mem_piAntidiag]; exact ⟨rfl, fun j _ => mem_univ j⟩
  have hle : Nat.multinomial univ a ≤ i ^ (∑ j, a j) := by
    rw [hsum]
    exact Finset.single_le_sum (f := fun k => Nat.multinomial univ k) (fun _ _ => Nat.zero_le _)
      hmem
  rw [← Nat.multinomial_spec]
  exact Nat.mul_le_mul_left _ hle

theorem MonomialNormLowerBound.factorial_le_pow_mul (i n : ℕ) (hi : 1 ≤ i) :
    (n + i - 1).factorial ≤ (n + i) ^ i * n.factorial * (i - 1).factorial := by
  have hk : n ≤ n + i - 1 := by omega
  have hsub : n + i - 1 - n = i - 1 := by omega
  have hspec := Nat.choose_mul_factorial_mul_factorial hk
  rw [hsub] at hspec
  have hch : (n + i - 1).choose n ≤ (n + i) ^ i := by
    rw [← Nat.choose_symm hk, hsub]
    calc (n + i - 1).choose (i - 1) ≤ (n + i - 1) ^ (i - 1) := Nat.choose_le_pow _ _
      _ ≤ (n + i) ^ (i - 1) := Nat.pow_le_pow_left (by omega) _
      _ ≤ (n + i) ^ i := Nat.pow_le_pow_right (by omega) (by omega)
  calc (n + i - 1).factorial = (n + i - 1).choose n * n.factorial * (i - 1).factorial := hspec.symm
    _ ≤ (n + i) ^ i * n.factorial * (i - 1).factorial := by gcongr

theorem MonomialNormLowerBound.proof : MonomialNormLowerBound.Statement := by
  intro i hi n a ha

  have hnat : (n + i - 1).factorial ≤
      (∏ j, (a j).factorial) * (i - 1).factorial * (i ^ n * (n + i) ^ i) := by
    have h1 := MonomialNormLowerBound.factorial_le_prod_mul_pow i a
    rw [ha] at h1
    calc (n + i - 1).factorial ≤ (n + i) ^ i * n.factorial * (i - 1).factorial :=
          MonomialNormLowerBound.factorial_le_pow_mul i n hi
      _ ≤ (n + i) ^ i * ((∏ j, (a j).factorial) * i ^ n) * (i - 1).factorial := by gcongr
      _ = (∏ j, (a j).factorial) * (i - 1).factorial * (i ^ n * (n + i) ^ i) := by ring
  have hi' : (0 : ℝ) < i := by exact_mod_cast hi
  have hA : (0 : ℝ) < (i : ℝ) ^ n * ((n : ℝ) + i) ^ i := by positivity
  have hF : (0 : ℝ) < ((n + i - 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hreal : ((n + i - 1).factorial : ℝ) ≤
      (∏ j, ((a j).factorial : ℝ)) * ((i - 1).factorial : ℝ) * ((i : ℝ) ^ n * ((n : ℝ) + i) ^ i) := by
    exact_mod_cast hnat
  rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast, ← mul_inv, inv_eq_one_div,
    div_le_div_iff₀ hA hF, one_mul]
  exact hreal

end GroundTheory.Heights₂.Heights
