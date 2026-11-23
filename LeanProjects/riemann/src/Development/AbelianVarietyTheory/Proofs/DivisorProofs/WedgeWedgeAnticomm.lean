import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicConnectionAddSection
open Matrix Set Filter Topology GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm
open scoped Real ContDiff

namespace GlobalTheory.WedgeAnticomm

theorem sgn_erase_of_mem {m : ℕ} {i : Fin m} (k : Fin m) {S : Finset (Fin m)} (hi : i ∈ S) :
    sgn k (S.erase i) = sgn k S * (if i < k then -1 else 1) := by
  unfold sgn
  rw [Finset.filter_erase]
  split_ifs with h
  · have hm : i ∈ S.filter (· < k) := Finset.mem_filter.2 ⟨hi, h⟩
    rw [Finset.card_erase_of_mem hm]
    have hpos : 0 < (S.filter (· < k)).card := Finset.card_pos.2 ⟨i, hm⟩
    obtain ⟨c, hc⟩ : ∃ c, (S.filter (· < k)).card = c + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
    rw [hc, Nat.add_sub_cancel, pow_succ, mul_assoc]; norm_num
  · have hm : i ∉ S.filter (· < k) := fun h' => h (Finset.mem_filter.1 h').2
    rw [Finset.erase_eq_of_notMem hm, mul_one]

theorem wedge_wedge_anticomm : ∀ {m : ℕ} (i k : Fin m) (w : Ext m),
    wedge i (wedge k w) = -wedge k (wedge i w) := by
  intro m i k w
  funext S
  simp only [wedge, Pi.neg_apply]
  by_cases hik : i = k
  · subst hik; simp
  by_cases hiS : i ∈ S
  · by_cases hkS : k ∈ S
    · have hk' : k ∈ S.erase i := Finset.mem_erase.2 ⟨Ne.symm hik, hkS⟩
      have hi' : i ∈ S.erase k := Finset.mem_erase.2 ⟨hik, hiS⟩
      rw [if_pos hiS, if_pos hk', if_pos hkS, if_pos hi', sgn_erase_of_mem k hiS,
        sgn_erase_of_mem i hkS, Finset.erase_right_comm]
      rcases lt_or_gt_of_ne hik with h | h
      · rw [if_pos h, if_neg (not_lt.2 h.le)]; ring
      · rw [if_neg (not_lt.2 h.le), if_pos h]; ring
    · have : k ∉ S.erase i := fun h => hkS (Finset.mem_of_mem_erase h)
      simp [hiS, hkS, this]
  · have : i ∉ S.erase k := fun h => hiS (Finset.mem_of_mem_erase h)
    simp [hiS, this]

end GlobalTheory.WedgeAnticomm
