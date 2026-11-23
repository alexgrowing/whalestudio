import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsComb
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Finset Comb

theorem CombTableauRowCount.proof : CombTableauRowCount.Statement := by
  intro m lam T t i
  unfold pcnt rowWord
  apply Finset.card_bij' (fun s _ => T.symm s) (fun p _ => T p)
  · intro s hs
    simp only [mem_filter, mem_univ, true_and, Equiv.apply_symm_apply] at hs ⊢
    exact ⟨hs.2, hs.1⟩
  · intro p hp
    simp only [mem_filter, mem_univ, true_and, Equiv.symm_apply_apply] at hp ⊢
    exact ⟨hp.2, hp.1⟩
  · intro s _
    simp
  · intro p _
    simp

end GroundTheory.Heights₂.Heights.RestTerms
