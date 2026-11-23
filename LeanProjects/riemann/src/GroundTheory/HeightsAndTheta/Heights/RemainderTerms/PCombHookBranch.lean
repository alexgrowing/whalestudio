import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsComb
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Finset Comb

theorem CombHookBranch.unconditional : CombHookBranch.Statement := by
  intro r s l hs hls hr a
  have ha := a.isLt
  by_cases hpos : 1 ≤ hookShape r (s + 1) l a
  · rw [if_pos hpos]
    by_cases ha0 : (a : ℕ) = 0
    · rw [if_neg (show ¬ ((a : ℕ) = l ∧ 1 ≤ l) by omega), add_zero]
      by_cases hl : l < s
      ·
        rw [if_pos ⟨ha0, hl⟩]
        have heq : Function.update (hookShape r (s + 1) l) a (hookShape r (s + 1) l a - 1)
            = hookShape r s l := by
          funext i
          simp only [Function.update_apply, hookShape, Fin.ext_iff]
          split_ifs <;> omega
        rw [heq]
      ·
        rw [if_neg (show ¬ ((a : ℕ) = 0 ∧ l < s) by omega),
          latticeWords_eq_empty_of_not_antitone, Finset.card_empty]
        intro hanti
        have key := hanti (show a ≤ (⟨1, by omega⟩ : Fin r) from
          Fin.le_iff_val_le_val.mpr (by show (a : ℕ) ≤ 1; omega))
        simp only [Function.update_apply, hookShape, Fin.ext_iff] at key
        split_ifs at key <;> omega
    · have hal : (a : ℕ) ≤ l := by
        simp only [hookShape] at hpos
        split_ifs at hpos <;> omega
      rw [if_neg (show ¬ ((a : ℕ) = 0 ∧ l < s) by omega), zero_add]
      by_cases hal' : (a : ℕ) = l
      ·
        rw [if_pos ⟨hal', by omega⟩]
        have heq : Function.update (hookShape r (s + 1) l) a (hookShape r (s + 1) l a - 1)
            = hookShape r s (l - 1) := by
          funext i
          simp only [Function.update_apply, hookShape, Fin.ext_iff]
          split_ifs <;> omega
        rw [heq]
      ·
        rw [if_neg (show ¬ ((a : ℕ) = l ∧ 1 ≤ l) by omega),
          latticeWords_eq_empty_of_not_antitone, Finset.card_empty]
        intro hanti
        have key := hanti (show a ≤ (⟨(a : ℕ) + 1, by omega⟩ : Fin r) from
          Fin.le_iff_val_le_val.mpr (by show (a : ℕ) ≤ (a : ℕ) + 1; omega))
        simp only [Function.update_apply, hookShape, Fin.ext_iff] at key
        split_ifs at key <;> omega
  ·
    rw [if_neg hpos]
    have hla : l < (a : ℕ) := by
      simp only [hookShape] at hpos
      split_ifs at hpos <;> omega
    rw [if_neg (show ¬ ((a : ℕ) = 0 ∧ l < s) by omega),
      if_neg (show ¬ ((a : ℕ) = l ∧ 1 ≤ l) by omega)]

theorem CombHookBranch.proof (_h1 : CombHookShapeFacts.Statement) : CombHookBranch.Statement :=
  CombHookBranch.unconditional

end GroundTheory.Heights₂.Heights.RestTerms
