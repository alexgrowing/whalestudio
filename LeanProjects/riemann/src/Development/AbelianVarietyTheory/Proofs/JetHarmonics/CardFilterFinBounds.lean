import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace

namespace GlobalTheory

theorem card_filter_fin_bounds {n : ℕ} (p : Fin n → Prop) [DecidablePred p] :
    (0 : ℝ) ≤ ((univ.filter p).card : ℝ) ∧ ((univ.filter p).card : ℝ) ≤ n := by
  refine ⟨Nat.cast_nonneg _, ?_⟩
  have h : (univ.filter p).card ≤ n :=
    le_trans (Finset.card_filter_le _ _) (by simp)
  exact_mod_cast h

theorem abs_lowK_sub_le {n : ℕ} (ε : Fin n → Bool) (μ : Fin n → ℝ) (a : Fin n) :
    -(n : ℝ) ≤ lowK ε μ a - μ a ∧ lowK ε μ a - μ a ≤ n := by
  have e : lowK ε μ a - μ a = rhoN ε a - rhoC ε a := by
    simp only [lowK, Pi.add_apply, Pi.sub_apply]
    ring
  rw [e]
  simp only [rhoN, rhoC]
  obtain ⟨h1, h2⟩ := card_filter_fin_bounds (fun b : Fin n => a < b ∧ ε b ≠ ε a)
  obtain ⟨h3, h4⟩ := card_filter_fin_bounds (fun b : Fin n => b < a ∧ ε b ≠ ε a)
  obtain ⟨h5, h6⟩ := card_filter_fin_bounds (fun b : Fin n => a < b ∧ ε b = ε a)
  obtain ⟨h7, h8⟩ := card_filter_fin_bounds (fun b : Fin n => b < a ∧ ε b = ε a)
  constructor <;> linarith

private lemma four_sq_add_le_of_large_bv {n : ℕ} {bv : ℝ} (hn : 2 ≤ n) (hb : 10 ^ 6 * (n : ℝ) ^ 7 ≤ bv) :
    4 * (n : ℝ) ^ 2 + 2 + n ≤ bv / 32 - bv / 100 := by
  have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have h7 : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 7 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have hsq : 4 * (n : ℝ) ^ 2 + 2 + n ≤ 6 * (n : ℝ) ^ 2 := by nlinarith
  linarith

theorem shape_position : ∀ (n kk j : ℕ) (ε : Fin n → Bool) (μ : Fin n → ℝ) (bv : ℝ), Shape ε kk μ bv → j ≤ 4 * n ^ 2 + 2 → 0 < bv ∧ (∀ ω : Fin n → ℝ, ∑ a, |ω a - lowK ε μ a| ≤ j → ∀ a : Fin n, (a.val + 1 < kk → -bv / 8 - bv / 32 ≤ -ω a ∧ -ω a ≤ bv / 32) ∧ (kk ≤ a.val + 1 → bv - bv / 32 ≤ -ω a ∧ -ω a ≤ 2 * bv + bv / 32)) ∧ ∀ a : Fin n, (a.val + 1 < kk → -bv / 8 - bv / 32 ≤ -μ a + (1 - (n : ℝ)) / 2 ∧ -μ a + (1 - (n : ℝ)) / 2 ≤ bv / 32) ∧ (kk ≤ a.val + 1 → bv - bv / 32 ≤ -μ a + (1 - (n : ℝ)) / 2 ∧ -μ a + (1 - (n : ℝ)) / 2 ≤ 2 * bv + bv / 32) := by
  intro n kk j ε μ bv hS hj
  obtain ⟨hk1, hkn, -, hcl, hnd, hb⟩ := hS
  have hn : 2 ≤ n := by omega
  have hm := four_sq_add_le_of_large_bv hn hb
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hbpos : 0 < bv := by
    have : (0 : ℝ) < (n : ℝ) ^ 7 := by positivity
    linarith
  have hjr : (j : ℝ) ≤ 4 * (n : ℝ) ^ 2 + 2 := by exact_mod_cast hj
  refine ⟨hbpos, ?_, ?_⟩
  · intro ω hω a
    have hle : |ω a - lowK ε μ a| ≤ j :=
      le_trans (Finset.single_le_sum (f := fun b => |ω b - lowK ε μ b|)
        (fun b _ => abs_nonneg _) (Finset.mem_univ a)) hω
    obtain ⟨hl1, hl2⟩ := abs_lowK_sub_le ε μ a
    obtain ⟨ha1, ha2⟩ := abs_le.mp hle
    constructor
    · intro ha
      obtain ⟨-, h1, h2⟩ := hcl a ha
      constructor <;> linarith
    · intro ha
      obtain ⟨h1, h2⟩ := hnd a ha
      constructor <;> linarith
  · intro a
    constructor
    · intro ha
      obtain ⟨-, h1, h2⟩ := hcl a ha
      constructor <;> linarith
    · intro ha
      obtain ⟨h1, h2⟩ := hnd a ha
      constructor <;> linarith

end GlobalTheory
