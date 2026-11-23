import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicConnectionAddSection
open Matrix Set Filter Topology GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm
open scoped Real ContDiff

namespace GlobalTheory.TorsionForm

theorem sgn_insert_of_notMem_ne {m : ℕ} {i : Fin m} (k : Fin m) {S : Finset (Fin m)} (hi : i ∉ S) :
    sgn k (insert i S) = sgn k S * (if i < k then -1 else 1) := by
  unfold sgn
  rw [Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp [hi]), pow_succ]
  · simp

theorem sgn_erase_of_mem_ne {m : ℕ} (i : Fin m) {k : Fin m} {S : Finset (Fin m)} (hk : k ∈ S) :
    sgn i (S.erase k) = sgn i S * (if k < i then -1 else 1) := by
  have h := sgn_insert_of_notMem_ne i (S := S.erase k) (Finset.notMem_erase k S)
  rw [Finset.insert_erase hk] at h
  split_ifs at h ⊢
  · linear_combination h
  · linear_combination -h

theorem contr_wedge_of_ne {m : ℕ} {i k : Fin m} (hik : i ≠ k) (w : Ext m) :
    contr i (wedge k w) = -wedge k (contr i w) := by
  funext S
  by_cases hiS : i ∈ S
  · have h1 : i ∈ S.erase k := Finset.mem_erase.2 ⟨hik, hiS⟩
    simp [contr, wedge, hiS, h1]
  · have hkS : k ∈ insert i S ↔ k ∈ S := by simp [Ne.symm hik]
    by_cases hk : k ∈ S
    · have h1 : i ∉ S.erase k := fun h => hiS (Finset.mem_of_mem_erase h)
      have hX : (insert i S).erase k = insert i (S.erase k) := Finset.erase_insert_of_ne hik
      simp only [contr, wedge, Pi.neg_apply, hiS, h1, hk, hkS.2 hk, if_true, if_false, hX,
        sgn_insert_of_notMem_ne k hiS, sgn_erase_of_mem_ne i hk]
      rcases lt_or_gt_of_ne hik with h | h
      · simp [h, not_lt.2 h.le]; ring
      · simp [h, not_lt.2 h.le]; ring
    · have : k ∉ insert i S := fun h => hk (hkS.1 h)
      simp [contr, wedge, hiS, hk, this]

end GlobalTheory.TorsionForm
