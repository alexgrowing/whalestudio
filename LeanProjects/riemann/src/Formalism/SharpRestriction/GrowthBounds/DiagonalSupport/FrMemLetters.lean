import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.RestValBdG
import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.LeCubeMul
import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.ImportsAlt
import Formalism.SharpRestriction.GrowthBounds.ValuationLowestDegreeMapFractionField

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.Proposition5Numerics

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords
open Formalism.MainNotions.G.WittFrameLocaliserOrders Formalism.MainNotions.G.symbolGeneratorData

section Ord

variable {n' r : ℕ} [NeZero n'] {Fr : Frames n' r} {L₁ N₁ : ℕ}

theorem llPos_lt (j : ℤ) (l l' : ℕ) (hll : l < l') (hl' : l' < (Fr.LLset j).card) : llPos Fr j l < llPos Fr j l' := by
  unfold llPos
  have hs := (Finset.sortedLT_sort (Fr.LLset j)).strictMono_get
  have hlen : ((Fr.LLset j).sort (· ≤ ·)).length = (Fr.LLset j).card := Finset.length_sort _
  have e : ∀ k (hk : k < (Fr.LLset j).card), ((Fr.LLset j).sort (· ≤ ·)).getD k 0 =
      ((Fr.LLset j).sort (· ≤ ·))[k]'(by rw [hlen]; exact hk) := by
    intro k hk
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem, hlen, hk]
  rw [e l (by omega), e l' hl']
  exact hs (a := ⟨l, by rw [hlen]; omega⟩) (b := ⟨l', by rw [hlen]; exact hl'⟩) hll

private theorem fr_le_fr_of_le_of_valid (hV : Fr.Valid L₁ N₁) (j : ℤ) :
    ∀ i i', i ≤ i' → i' < r → Fr.fr j i ≤ Fr.fr j i' := by
  intro i i' hii' hi'
  induction i', hii' using Nat.le_induction with
  | base => exact le_rfl
  | succ k hik ih => exact (ih (by omega)).trans (hV.2.2.1 j k (by omega)).le

private theorem llPos_mem_LLset' (j : ℤ) (l : ℕ) (hl : l < (Fr.LLset j).card) : llPos Fr j l ∈ Fr.LLset j := by
  unfold llPos
  have hlen : ((Fr.LLset j).sort (· ≤ ·)).length = (Fr.LLset j).card := Finset.length_sort _
  have e : ((Fr.LLset j).sort (· ≤ ·)).getD l 0 =
      ((Fr.LLset j).sort (· ≤ ·))[l]'(by rw [hlen]; exact hl) := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem, hlen, hl]
  rw [e, ← Finset.mem_sort (· ≤ ·)]
  exact List.getElem_mem _

theorem posU_lt (hV : Fr.Valid L₁ N₁) (j : ℤ) (a b : ℕ) (hab : a < b) (hb : b < (Fr.LLset j).card + r) :
    posU Fr (Fr.LLset j).card j a < posU Fr (Fr.LLset j).card j b := by
  have hm := fr_le_fr_of_le_of_valid hV j
  unfold posU
  split_ifs with ha hb hb
  · exact llPos_lt j a b hab hb
  · have h1 := llPos_mem_LLset' j a ha
    simp only [Frames.LLset, Finset.mem_filter, Finset.mem_Ioo] at h1
    exact lt_of_lt_of_le h1.1.2 (hm 0 (b - (Fr.LLset j).card) (Nat.zero_le _) (by omega))
  · omega
  · exact (hV.2.2.1 j (a - (Fr.LLset j).card) (by omega)).trans_le (hm _ _ (by omega) (by omega))

theorem posU_lt_iff (hV : Fr.Valid L₁ N₁) (j : ℤ) (a b : ℕ) (ha : a < (Fr.LLset j).card + r)
    (hb : b < (Fr.LLset j).card + r) :
    posU Fr (Fr.LLset j).card j a < posU Fr (Fr.LLset j).card j b ↔ a < b := by
  refine ⟨fun h => ?_, fun h => posU_lt hV j a b h hb⟩
  by_contra hn
  push_neg at hn
  rcases hn.lt_or_eq with h2 | h2
  · exact lt_asymm h (posU_lt hV j b a h2 ha)
  · subst h2
    exact lt_irrefl _ h

theorem posU_le_iff (hV : Fr.Valid L₁ N₁) (j : ℤ) (a b : ℕ) (ha : a < (Fr.LLset j).card + r)
    (hb : b < (Fr.LLset j).card + r) :
    posU Fr (Fr.LLset j).card j a ≤ posU Fr (Fr.LLset j).card j b ↔ a ≤ b := by
  rw [← not_lt, posU_lt_iff hV j b a hb ha, not_lt]

theorem posU_ll (j : ℤ) (l : ℕ) (hl : l < (Fr.LLset j).card) : posU Fr (Fr.LLset j).card j l = llPos Fr j l := by
  unfold posU
  rw [if_pos hl]

theorem posU_fr (j : ℤ) (i : ℕ) : posU Fr (Fr.LLset j).card j ((Fr.LLset j).card + i) = Fr.fr j i := by
  unfold posU
  rw [if_neg (by omega), Nat.add_sub_cancel_left]

theorem w_lt_posU (hV : Fr.Valid L₁ N₁) (hr : 1 ≤ r) (j : ℤ) (i u : ℕ) (hi : i < r) (hu : u < (Fr.LLset j).card + r) :
    Fr.fr (j - 1) i < posU Fr (Fr.LLset j).card j u := by
  have hfi : Fr.fr (j - 1) i ≤ Fr.fr (j - 1) (r - 1) := fr_le_fr_of_le_of_valid hV (j - 1) i (r - 1) (by omega) (by omega)
  have hgap : Fr.fr (j - 1) (r - 1) < Fr.fr j 0 := by
    have h1 := hV.2.2.2.1 (j - 1)
    rwa [sub_add_cancel] at h1
  unfold posU
  split_ifs with hu'
  · have h1 := llPos_mem_LLset' j u hu'
    simp only [Frames.LLset, Finset.mem_filter, Finset.mem_Ioo] at h1
    exact lt_of_le_of_lt hfi h1.1.1
  · exact lt_of_le_of_lt hfi (lt_of_lt_of_le hgap (fr_le_fr_of_le_of_valid hV j 0 _ (Nat.zero_le _) (by omega)))

theorem fr_mem_letters (hV : Fr.Valid L₁ N₁) (hr : 1 ≤ r) (j : ℤ) (i : ℕ) (hi : i < r) : Fr.fr j i ∈ Fr.letters j := by
  have hm0 := fr_le_fr_of_le_of_valid hV (j - 1)
  have hm := fr_le_fr_of_le_of_valid hV j
  have hgap : Fr.fr (j - 1) (r - 1) < Fr.fr j 0 := by
    have h1 := hV.2.2.2.1 (j - 1)
    rwa [sub_add_cancel] at h1
  simp only [Frames.letters, Finset.mem_filter, Finset.mem_Icc]
  refine ⟨⟨?_, hm i (r - 1) (by omega) (by omega)⟩, (hV.2.2.2.2.1 j i hi).1⟩
  exact (hm0 0 (r - 1) (Nat.zero_le _) (by omega)).trans (hgap.le.trans (hm 0 i (Nat.zero_le _) hi))

theorem w_mem_letters (hV : Fr.Valid L₁ N₁) (hr : 1 ≤ r) (j : ℤ) (i : ℕ) (hi : i < r) :
    Fr.fr (j - 1) i ∈ Fr.letters j := by
  have hm0 := fr_le_fr_of_le_of_valid hV (j - 1)
  have hm := fr_le_fr_of_le_of_valid hV j
  have hgap : Fr.fr (j - 1) (r - 1) < Fr.fr j 0 := by
    have h1 := hV.2.2.2.1 (j - 1)
    rwa [sub_add_cancel] at h1
  simp only [Frames.letters, Finset.mem_filter, Finset.mem_Icc]
  refine ⟨⟨hm0 0 i (Nat.zero_le _) hi, ?_⟩, (hV.2.2.2.2.1 (j - 1) i hi).1⟩
  exact (hm0 i (r - 1) (by omega) (by omega)).trans
    (hgap.le.trans (hm 0 (r - 1) (Nat.zero_le _) (by omega)))

end Ord

end Formalism.MainNotions.Proposition5Numerics
