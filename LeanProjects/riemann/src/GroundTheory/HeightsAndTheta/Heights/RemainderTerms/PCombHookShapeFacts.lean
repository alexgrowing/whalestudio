import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsComb
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Finset

theorem CombHookShapeFacts.sum_lt_indicator (l : ℕ) :
    ∀ m : ℕ, (∑ i ∈ range m, if i < l then 1 else 0) = min m l := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, ih]
    split_ifs <;> omega

theorem CombHookShapeFacts.proof : CombHookShapeFacts.Statement := by
  intro r s l hls hsr
  refine ⟨?_, ?_⟩
  · intro i j hij
    have hij' : (i : ℕ) ≤ j := hij
    simp only [hookShape]
    split_ifs <;> omega
  · obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
    have h := Fin.sum_univ_eq_sum_range
      (fun k : ℕ => if k = 0 then s - l else if k ≤ l then 1 else 0) (m + 1)
    simp only [hookShape]
    rw [h, sum_range_succ']
    have h2 : (∑ i ∈ range m, (if i + 1 = 0 then s - l else if i + 1 ≤ l then 1 else 0)) =
        ∑ i ∈ range m, (if i < l then 1 else 0) := by
      refine sum_congr rfl fun i _ => ?_
      rw [if_neg (Nat.succ_ne_zero i)]
      split_ifs <;> omega
    rw [h2, CombHookShapeFacts.sum_lt_indicator l m]
    simp only [if_true]
    omega

end GroundTheory.Heights₂.Heights.RestTerms
