import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScaledBoxRadiiAtEntry

open ValuativeRel Matrix GlobalTheory.SplitFlip GlobalTheory.FullRankCoinv GlobalTheory.RankCoinv GlobalTheory.NormalCore

noncomputable section
namespace GlobalTheory.ScaleBoxPre

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem val_unit_pow (ϖ : kˣ) (m : ℕ) : valuation k ((ϖ ^ m : kˣ) : k) = valuation k (ϖ : k) ^ m := by
  rw [Units.val_pow_eq_pow_val, map_pow]

theorem le_shift_down {ϖ : kˣ} {y : k} {N : ℕ} (hN : 1 ≤ N) :
    valuation k ((ϖ : k) * y) ≤ valuation k ((ϖ ^ N : kˣ) : k) ↔
      valuation k y ≤ valuation k ((ϖ ^ (N - 1) : kˣ) : k) := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  rw [val_unit_pow, val_unit_pow, Nat.add_sub_cancel, map_mul, pow_succ', mul_comm (valuation k (ϖ : k)),
    mul_comm (valuation k (ϖ : k)) (valuation k (ϖ : k) ^ M)]
  have h0 : 0 < valuation k (ϖ : k) := zero_lt_iff.2 (by simp)
  rw [← mul_inv_le_iff₀ h0, mul_inv_cancel_right₀ h0.ne']

theorem le_shift_up {ϖ : kˣ} {y : k} {N : ℕ} :
    valuation k (y * ((ϖ⁻¹ : kˣ) : k)) ≤ valuation k ((ϖ ^ N : kˣ) : k) ↔
      valuation k y ≤ valuation k ((ϖ ^ (N + 1) : kˣ) : k) := by
  rw [val_unit_pow, val_unit_pow, map_mul, pow_succ, Units.val_inv_eq_inv_val, map_inv₀]
  have h0 : 0 < valuation k (ϖ : k) := zero_lt_iff.2 (by simp)
  exact mul_inv_le_iff₀ h0

theorem entry_scale {n d : ℕ} (i₀ : Fin n) (j₀ : Fin d) (ϖ : kˣ) (Y : Matrix (Fin n) (Fin d) k) (i : Fin n)
    (j : Fin d) : (((dgl i₀ ϖ).1)ᵀ * Y * (dgl j₀ ϖ⁻¹).1) i j =
      Function.update (1 : Fin n → k) i₀ (ϖ : k) i * Y i j * Function.update (1 : Fin d → k) j₀ ((ϖ⁻¹ : kˣ) : k) j := by
  simp only [dgl_val, diagonal_transpose, diagonal_mul, mul_diagonal]

theorem entry_scale_right {n d : ℕ} (j₀ : Fin d) (ϖ : kˣ) (Y : Matrix (Fin n) (Fin d) k) (i : Fin n)
    (j : Fin d) : (Y * (dgl j₀ ϖ⁻¹).1) i j = Y i j * Function.update (1 : Fin d → k) j₀ ((ϖ⁻¹ : kˣ) : k) j := by
  simp only [dgl_val, mul_diagonal]

theorem preimage_box_scale_eq_ebox (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n d : ℕ) (i₀ : Fin n) (j₀ : Fin d) (ϖ : kˣ)
    (p₁ p₂ : Matrix (Fin n) (Fin d) k) (N : ℕ) (hN : 1 ≤ N)
    (h₁ : ∀ j, p₁ i₀ j = if j = j₀ then 1 else 0) (h₁' : ∀ i, i ≠ i₀ → p₁ i j₀ = 0) (h₂ : ∀ i, p₂ i j₀ = 0) :
    {Y : Matrix (Fin n) (Fin d) k | ((dgl i₀ ϖ).1)ᵀ * Y * (dgl j₀ ϖ⁻¹).1 ∈ box ϖ p₁ (fun _ => N)} =
        ebox ϖ p₁ (scaledBoxRadiiAtEntry i₀ j₀ N) ∧
      {Y : Matrix (Fin n) (Fin d) k | Y * (dgl j₀ ϖ⁻¹).1 ∈ box ϖ p₂ (fun _ => N)} = ebox ϖ p₂ (baseCellRadiiAtColumn j₀ N) := by
  have hu : (ϖ : k) * ((ϖ⁻¹ : kˣ) : k) = 1 := Units.mul_inv ϖ
  constructor
  · ext Y
    simp only [Set.mem_setOf_eq, box, ebox]
    refine forall₂_congr fun i j => ?_
    rw [entry_scale]
    by_cases hi : i = i₀ <;> by_cases hj : j = j₀
    · subst hi hj
      have e : (ϖ : k) * Y i j * ((ϖ⁻¹ : kˣ) : k) = Y i j := by
        rw [mul_comm (ϖ : k), mul_assoc, hu, mul_one]
      simp only [Function.update_self, e, scaledBoxRadiiAtEntry, ne_eq, not_true_eq_false, and_false, and_false, if_false]
    · subst hi
      rw [h₁ j, if_neg hj, Function.update_self, Function.update_of_ne hj, Pi.one_apply, mul_one, sub_zero,
        sub_zero, le_shift_down hN]
      simp only [scaledBoxRadiiAtEntry, hj, ne_eq, not_false_eq_true, and_self, if_true]
    · subst hj
      rw [h₁' i hi, Function.update_self, Function.update_of_ne hi, Pi.one_apply, one_mul, sub_zero, sub_zero,
        le_shift_up]
      simp only [scaledBoxRadiiAtEntry, hi, ne_eq, not_false_eq_true, and_self, if_true, false_and, if_false]
    · rw [Function.update_of_ne hi, Function.update_of_ne hj, Pi.one_apply, Pi.one_apply, one_mul, mul_one]
      simp only [scaledBoxRadiiAtEntry, hi, hj, ne_eq, not_false_eq_true, false_and, and_false, if_false]
  · ext Y
    simp only [Set.mem_setOf_eq, box, ebox]
    refine forall₂_congr fun i j => ?_
    rw [entry_scale_right]
    by_cases hj : j = j₀
    · subst hj
      rw [h₂ i, Function.update_self, sub_zero, sub_zero, le_shift_up]
      simp only [baseCellRadiiAtColumn, if_true]
    · rw [Function.update_of_ne hj, Pi.one_apply, mul_one]
      simp only [baseCellRadiiAtColumn, hj, if_false]

end GlobalTheory.ScaleBoxPre
