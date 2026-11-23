import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsComb
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Comb

theorem CombCfUpdateZero.proof : CombCfUpdateZero.Statement := by
  intro m A hA lam hlam i hpos hcase

  have key : (i : ℕ) + 1 < m ∧ ∀ h : (i : ℕ) + 1 < m, lam ⟨i + 1, h⟩ = lam i := by
    by_cases h0 : lam i = 0
    · have hs : 1 ≤ stair m i := by omega
      simp only [stair] at hs
      refine ⟨by omega, fun h => ?_⟩
      have := hlam (show i ≤ (⟨i + 1, h⟩ : Fin m) from Fin.le_iff_val_le_val.mpr (by simp))
      omega
    · have hna : ¬ Antitone (Function.update lam i (lam i - 1)) := by
        rcases hcase with h | h
        · exact absurd h h0
        · exact h
      have hK : ∃ b : Fin m, i < b ∧ lam i ≤ lam b := by
        by_contra hK
        push Not at hK
        apply hna
        intro a b hab
        simp only [Function.update_apply]
        split_ifs with hb ha ha
        · exact le_rfl
        · have := hlam (show a ≤ i from hb ▸ hab)
          omega
        · have hib : i < b := lt_of_le_of_ne (ha ▸ hab) (fun e => hb e.symm)
          have := hK b hib
          omega
        · exact hlam hab
      obtain ⟨b, hib, hb⟩ := hK
      have hib' : (i : ℕ) < b := hib
      have hm : (i : ℕ) + 1 < m := by have := b.isLt; omega
      refine ⟨hm, fun h => ?_⟩
      have h1 := hlam (show i ≤ (⟨i + 1, h⟩ : Fin m) from Fin.le_iff_val_le_val.mpr (by simp))
      have h2 := hlam (show (⟨i + 1, h⟩ : Fin m) ≤ b from Fin.le_iff_val_le_val.mpr (by simp; omega))
      omega
  obtain ⟨hm, heq⟩ := key
  have hne : i ≠ (⟨i + 1, hm⟩ : Fin m) := by
    intro e
    have := congrArg Fin.val e
    simp at this
  apply cf_eq_zero_of_eq hA hne
  rw [Function.update_self, Function.update_of_ne hne.symm, heq hm]
  simp only [stair] at hpos ⊢
  omega

end GroundTheory.Heights₂.Heights.RestTerms
