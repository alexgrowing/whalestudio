import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsComb
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Finset Comb

theorem CombTableauRowPrefix.proof : CombTableauRowPrefix.Statement := by
  intro m lam T hT t
  set c := T.symm t with hc
  have hTc : T c = t := by simp [hc]
  have key : ∀ p : youngCells lam, p.1.1 = c.1.1 →
      ((T p : ℕ) < (t : ℕ) ↔ p.1.2 < c.1.2) := by
    intro p hp
    constructor
    · intro hlt
      by_contra hle'
      have hle := not_lt.mp hle'
      have h := hT c p hp.symm.le hle
      rw [hTc] at h
      exact absurd hlt (not_lt.mpr (Fin.le_def.mp h))
    · intro hlt
      have hle : T p ≤ T c := hT p c hp.le hlt.le
      have hne : p ≠ c := by
        intro h
        rw [h] at hlt
        exact lt_irrefl _ hlt
      have hne' : T p ≠ T c := fun h => hne (T.injective h)
      rw [hTc] at hle hne'
      exact Fin.lt_def.mp (lt_of_le_of_ne hle hne')
  have hcmem : c.1 ∈ youngCells lam := c.2
  simp only [youngCells, mem_filter, mem_product, mem_univ, true_and, mem_range] at hcmem
  rw [show (univ.filter fun p : youngCells lam => p.1.1 = c.1.1 ∧ (T p : ℕ) < (t : ℕ)) =
      univ.filter fun p : youngCells lam => p.1.1 = c.1.1 ∧ p.1.2 < c.1.2 from
    filter_congr fun p _ => and_congr_right (key p)]
  refine Eq.trans ?_ (card_range c.1.2)
  refine card_bij (fun p _ => p.1.2) ?_ ?_ ?_
  · intro p hp
    simp only [mem_filter, mem_univ, true_and] at hp
    exact mem_range.mpr hp.2
  · intro p hp q hq hpq
    simp only [mem_filter, mem_univ, true_and] at hp hq
    exact Subtype.ext (Prod.ext (hp.1.trans hq.1.symm) hpq)
  · intro k hk
    rw [mem_range] at hk
    refine ⟨⟨(c.1.1, k), ?_⟩, ?_, rfl⟩
    · simp only [youngCells, mem_filter, mem_product, mem_univ, true_and, mem_range]
      exact ⟨by omega, by omega⟩
    · simp [hk]

end GroundTheory.Heights₂.Heights.RestTerms
