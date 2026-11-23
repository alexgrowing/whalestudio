import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.SlackBoundReal

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.Proposition5Numerics

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords
open Formalism.MainNotions.G.WittFrameLocaliserOrders Formalism.MainNotions.G.symbolGeneratorData

variable {n' r : ℕ} [NeZero n'] (Fr : Frames n' r) {L₁ N₁ : ℕ} {J : ℕ} [NeZero J] {nL : ZMod J → ℕ}

theorem llPos_surj (j y : ℤ) (hy : y ∈ Fr.LLset j) : ∃ l, l < (Fr.LLset j).card ∧ llPos Fr j l = y := by
  have hm : y ∈ (Fr.LLset j).sort (· ≤ ·) := (Finset.mem_sort _).mpr hy
  obtain ⟨i, hi, hiy⟩ := List.mem_iff_getElem.mp hm
  refine ⟨i, by rwa [Finset.length_sort] at hi, ?_⟩
  unfold Formalism.MainNotions.TestSideWords.llPos
  rw [List.getD_eq_getElem _ _ hi, hiy]

theorem posTL_surj (hV : Fr.Valid L₁ N₁) (hr : 1 ≤ r) (hJ : J = Fr.J) (hnL : ∀ j, nL j = (Fr.LLset (segZ j)).card)
    (s : Fin n') (hs : s ∈ Fr.TT) : ∃ x : TL J nL r, posOf n' (posTL Fr x) = s := by
  have hper : Fr.fr ((Fr.J : ℤ) - 1) (r - 1) = Fr.fr (-1) (r - 1) + n' := by
    have := hV.2.1 (-1) (r - 1)
    rw [← this]; congr 1
  set c : ℤ := Fr.fr (-1) (r - 1) + 1 with hc
  have hn0 : (0 : ℤ) < n' := by exact_mod_cast NeZero.pos n'
  have b1 := Int.emod_nonneg ((s.val : ℤ) - c) hn0.ne'
  have b2 := Int.emod_lt_of_pos ((s.val : ℤ) - c) hn0
  have b3 := Int.emod_def ((s.val : ℤ) - c) n'
  have hx0 : c + ((s.val : ℤ) - c) % n' = (s.val : ℤ) + n' * (-(((s.val : ℤ) - c) / n')) := by
    rw [b3]; ring
  have hp : posOf n' (c + ((s.val : ℤ) - c) % n') = s := by
    rw [hx0, posOf_add_mul_alt, posOf_natCast_self]
  set y : ℤ := c + ((s.val : ℤ) - c) % n' with hy
  have hyT : posOf n' y ∈ Fr.TT := by rw [hp]; exact hs
  obtain ⟨j, h1, h2⟩ := mn_cover Fr L₁ N₁ hV hr y hyT
  have h3 : y ∈ nonW Fr j := by
    unfold nonW; rw [Finset.mem_filter]; exact ⟨h1, h2⟩
  have h4 := (ph_mem_nonW Fr hV hr _ _).1 h3
  have j0 : 0 ≤ j := by
    by_contra h
    have := ph_z_mono Fr hV hr (j := j) (j' := -1) (by omega)
    omega
  have j1 : j < Fr.J := by
    by_contra h
    have := ph_z_mono Fr hV hr (j := (Fr.J : ℤ) - 1) (j' := j - 1) (by omega)
    omega
  set jj : ZMod J := (j.toNat : ZMod J) with hjj
  have hseg : segZ jj = j := by
    unfold segZ
    rw [hjj, ZMod.val_natCast_of_lt (by rw [hJ]; omega)]
    omega
  rcases lt_or_ge y (Fr.fr j 0) with hlt | hge
  · have hyL : y ∈ Fr.LLset (segZ jj) := by
      rw [hseg]
      exact (mem_LLset Fr _ _).2 ⟨⟨h4.1, hlt⟩, hyT⟩
    obtain ⟨l, hl, he⟩ := llPos_surj Fr _ _ hyL
    refine ⟨⟨jj, Sum.inl ⟨l, by rw [hnL]; exact hl⟩⟩, ?_⟩
    show posOf n' (llPos Fr (segZ jj) l) = s
    rw [he]; exact hp
  · obtain ⟨i, hi, he⟩ := ge_frame Fr L₁ N₁ hV j y hyT hge (r - 1) (by omega) h4.2.1
    refine ⟨⟨jj, Sum.inr ⟨r - 1 - i, by omega⟩⟩, ?_⟩
    show posOf n' (Fr.fr (segZ jj) (r - 1 - (r - 1 - i))) = s
    have e : r - 1 - (r - 1 - i) = i := by omega
    rw [e, hseg, ← he]; exact hp

end Formalism.MainNotions.Proposition5Numerics
