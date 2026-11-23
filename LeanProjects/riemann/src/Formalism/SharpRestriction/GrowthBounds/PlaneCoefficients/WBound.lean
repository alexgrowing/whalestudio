import Formalism.SharpRestriction.GrowthBounds.TwistedSubstitution.WordLossNonneg

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.PairMembershipBlocks

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords
open Formalism.MainNotions.G.WittFrameLocaliserOrders

theorem sum_ite_mem {α β : Type*} [DecidableEq α] (f : β → α) (T : Finset α) (l : List β) :
    (l.map fun z => if f z ∈ T then (2 : ℝ) else 0).sum =
      2 * ∑ s ∈ T, ((l.filter fun z => f z = s).length : ℝ) := by
  induction l with
  | nil => simp
  | cons y l ih =>
    have e : ∀ s, (((y :: l).filter fun z => f z = s).length : ℝ) =
        ((l.filter fun z => f z = s).length : ℝ) + if f y = s then 1 else 0 := by
      intro s
      by_cases h : f y = s
      · simp [h]
      · simp [h]
    simp only [List.map_cons, List.sum_cons, ih, e, Finset.sum_add_distrib, Finset.sum_ite_eq]
    split_ifs <;> ring

section Geo

variable {n' r : ℕ} [NeZero n'] (Fr : Frames n' r)

theorem llPos_mem (j : ℤ) (l : ℕ) (hl : l < (Fr.LLset j).card) : llPos Fr j l ∈ Fr.LLset j := by
  unfold llPos
  have hlen : ((Fr.LLset j).sort (· ≤ ·)).length = (Fr.LLset j).card := Finset.length_sort _
  rw [List.getD_eq_getElem _ _ (by rw [hlen]; exact hl)]
  exact (Finset.mem_sort (· ≤ ·)).1 (List.getElem_mem _)

theorem mem_LLset (j x : ℤ) : x ∈ Fr.LLset j ↔
    (Fr.fr (j - 1) (r - 1) < x ∧ x < Fr.fr j 0) ∧ posOf n' x ∈ Fr.TT := by
  unfold Frames.LLset
  simp only [Finset.mem_filter, Finset.mem_Ioo]

variable {Fr} {L₁ N₁ : ℕ}

theorem LL_sub_letters (hV : Fr.Valid L₁ N₁) (hr : 1 ≤ r) (j y : ℤ) (hy : y ∈ Fr.LLset j) :
    y ∈ Fr.letters j ∧ ¬ Fr.IsW j y := by
  have h := (mem_LLset Fr _ _).1 hy
  have h1 := frame_row_monotone Fr L₁ N₁ hV (j - 1) (r - 1) (by omega)
  have h2 := frame_row_monotone Fr L₁ N₁ hV j (r - 1) (by omega)
  refine ⟨?_, ?_⟩
  · unfold Frames.letters
    simp only [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨by omega, by omega⟩, h.2⟩
  · unfold Frames.IsW
    omega

theorem posU_mem (hV : Fr.Valid L₁ N₁) (hr : 1 ≤ r) (j : ℤ) (u : ℕ) (hu : u < (Fr.LLset j).card + r) :
    posU Fr (Fr.LLset j).card j u ∈ Fr.letters j ∧ ¬ Fr.IsW j (posU Fr (Fr.LLset j).card j u) := by
  unfold posU
  split_ifs with h
  · exact LL_sub_letters hV hr j _ (llPos_mem Fr j u h)
  · have hi : u - (Fr.LLset j).card < r := by omega
    have h1 := hV.2.2.2.1 (j - 1)
    rw [sub_add_cancel] at h1
    have h2 := frame_row_monotone Fr L₁ N₁ hV (j - 1) (r - 1) (by omega)
    have h3 := frame_row_monotone Fr L₁ N₁ hV j _ hi
    have h4 := frame_entry_le_last Fr L₁ N₁ hV j _ hi
    refine ⟨?_, ?_⟩
    · unfold Frames.letters
      simp only [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨by omega, h4⟩, (hV.2.2.2.2.1 j _ hi).1⟩
    · unfold Frames.IsW
      omega

theorem Bo_ge (hV : Fr.Valid L₁ N₁) (hr : 1 ≤ r) (p : ℕ) (hp : 1 ≤ p) (deg : Fin n' → ℕ) (a : ℝ)
    (hdeg : ∀ s ∈ Fr.TT, a ≤ (deg s : ℝ)) (G : ℕ) (j x : ℤ) (hG : Fr.fr j (r - 1) - Fr.fr (j - 1) 0 ≤ G)
    (hx : x ∈ Fr.letters j) (hW : ¬ Fr.IsW j x) :
    a / (p : ℝ) ^ G ≤ Bo p Fr deg j x := by
  have hy := oldest_mem_segment_letters Fr L₁ N₁ hV hr j x hx hW
  unfold Frames.letters at hy
  simp only [Finset.mem_filter, Finset.mem_Icc] at hy
  have hp' : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  unfold Bo levDeg
  apply div_le_div₀ (Nat.cast_nonneg _) (hdeg _ hy.2) (by positivity)
  apply pow_le_pow_right₀ hp'
  unfold Frames.dist
  omega

theorem wordLoss_le {k : ℕ} (l : List (Fin n' × (Fin k × Fin k))) (c0 : ℕ)
    (hc : ∀ s, (l.filter fun z => z.1 = s).length ≤ c0) (jz : ℤ) (u : ℕ) :
    wordLoss Fr l jz u ≤ 2 * ((Fr.letters jz).card : ℝ) * c0 := by
  set T : Finset (Fin n') := (Fr.letters jz).image (posOf n') with hT
  have h1 : wordLoss Fr l jz u ≤ (l.map fun z => if z.1 ∈ T then (2 : ℝ) else 0).sum := by
    unfold wordLoss
    apply List.sum_le_sum
    intro z _
    unfold opCost
    by_cases ht : touchT Fr jz u z.1
    · obtain ⟨x, hx, hxs, _⟩ := ht
      have hm : z.1 ∈ T := by
        rw [hT]
        exact Finset.mem_image.2 ⟨x, hx, hxs⟩
      rw [if_pos ⟨x, hx, hxs, by assumption⟩, if_pos hm]
    · rw [if_neg ht]
      split_ifs <;> norm_num
  have h2 := sum_ite_mem (fun z : Fin n' × (Fin k × Fin k) => z.1) T l
  have h3 : ∑ s ∈ T, ((l.filter fun z => z.1 = s).length : ℝ) ≤ ∑ _s ∈ T, (c0 : ℝ) := by
    apply Finset.sum_le_sum
    intro s _
    exact_mod_cast hc s
  have h4 : (T.card : ℝ) ≤ ((Fr.letters jz).card : ℝ) := by
    exact_mod_cast Finset.card_image_le
  rw [Finset.sum_const, nsmul_eq_mul] at h3
  have h5 : (T.card : ℝ) * c0 ≤ ((Fr.letters jz).card : ℝ) * c0 :=
    mul_le_mul_of_nonneg_right h4 (Nat.cast_nonneg _)
  rw [h2] at h1
  nlinarith

end Geo

theorem size_arith (C k r N Q cS c0 e Y N1 : ℝ) (hC : 16 ≤ C) (hk : 1 ≤ k) (hr : 1 ≤ r) (hN : 1 ≤ N) (hQ : 1 ≤ Q)
    (hcS : 0 ≤ cS) (hc0 : 0 ≤ c0) (he : 0 ≤ e) (hY : 0 ≤ Y) (hN1 : 0 ≤ N1) (hN1' : N1 ≤ r * N) :
    16 * N1 * c0 * (Y * k ^ 2) * Q ≤ C * k ^ 3 * r ^ 2 * N * Q ^ 5 * (cS + (r * N * c0 + e)) * Y := by
  have a1 : k ^ 2 ≤ k ^ 3 := pow_le_pow_right₀ hk (by norm_num)
  have a2 : Q ≤ Q ^ 5 := le_self_pow₀ hQ (by norm_num)
  have a3 : (1 : ℝ) ≤ r ^ 2 := one_le_pow₀ hr
  have a4 : N1 * c0 ≤ cS + (r * N * c0 + e) := by
    have := mul_le_mul_of_nonneg_right hN1' hc0
    linarith
  have b1 : 16 * k ^ 2 ≤ C * k ^ 3 := mul_le_mul hC a1 (by positivity) (by linarith)
  have b2 : 16 * k ^ 2 ≤ C * k ^ 3 * r ^ 2 := le_trans b1 (le_mul_of_one_le_right (by positivity) a3)
  have b3 : 16 * k ^ 2 ≤ C * k ^ 3 * r ^ 2 * N := le_trans b2 (le_mul_of_one_le_right (by positivity) hN)
  have b4 : 16 * k ^ 2 * Q ≤ C * k ^ 3 * r ^ 2 * N * Q ^ 5 := mul_le_mul b3 a2 (by linarith) (by positivity)
  have b5 : 16 * k ^ 2 * Q * (N1 * c0) ≤ C * k ^ 3 * r ^ 2 * N * Q ^ 5 * (cS + (r * N * c0 + e)) :=
    mul_le_mul b4 a4 (by positivity) (by positivity)
  have b6 := mul_le_mul_of_nonneg_right b5 hY
  calc 16 * N1 * c0 * (Y * k ^ 2) * Q = 16 * k ^ 2 * Q * (N1 * c0) * Y := by ring
    _ ≤ _ := b6

theorem wordBoundStep (C CLa : ℝ) (hC : 16 ≤ C) : WordBoundStep C CLa := by
  intro p W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w n' m r _ _ TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar K _ _ hk hrk
    F nb B hD l _ hc jz u hu
  obtain ⟨_, H, hF, _⟩ := hD
  have hB := hyps_basic (by linarith : (1 : ℝ) ≤ C) H
  obtain ⟨h1, h2, _, h4, h5, h6, _, _, _, _, _, h12⟩ := H
  obtain ⟨hTT, hV, hG, _⟩ := hF
  have hr1 : 1 ≤ r := by omega
  have ha0 : (0 : ℝ) ≤ a := by linarith [hB.two_le_a]
  obtain ⟨hx, hW⟩ := posU_mem hV hr1 jz u hu
  set xx := posU F (F.LLset jz).card jz u with hxx

  have hw := wordLoss_le (Fr := F) l c0 hc jz u
  have hcard : ((F.letters jz).card : ℝ) ≤ (orbitWindowCount r de h x : ℝ) := by exact_mod_cast hV.2.2.2.2.2.2.2.1 jz
  have hw2 : wordLoss F l jz u ≤ 2 * (orbitWindowCount r de h x : ℝ) * c0 := by
    have := mul_le_mul_of_nonneg_right hcard (Nat.cast_nonneg c0 : (0 : ℝ) ≤ c0)
    linarith

  have hdeg : ∀ s ∈ F.TT, a ≤ (flatDeg lam0 s : ℝ) := by
    intro s hs
    rw [hTT] at hs
    exact (flatDeg_bounds (by have := hB.m_ge; omega) ha0 h5 s hs).1
  have hBo := Bo_ge hV hr1 p (by omega) (flatDeg lam0) a hdeg (goodG' r de h x) jz xx (le_of_lt (hG jz)) hx hW

  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (by omega : 1 ≤ p)
  have hQ1 : (1 : ℝ) ≤ (p : ℝ) ^ goodG' r de h x := one_le_pow₀ hp1
  have hk1 : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ m + 1)
  have hrr : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
  have hNN : (1 : ℝ) ≤ (TT.card : ℝ) := by exact_mod_cast hB.N_pos
  have hY0 : (0 : ℝ) < Y := by linarith [hB.two_le_Y]
  have hN1 : ((orbitWindowCount r de h x : ℕ) : ℝ) ≤ (r : ℝ) * TT.card := by
    have : orbitWindowCount r de h x ≤ r * TT.card := le_trans (Nat.le_self_pow (by norm_num) _) h4
    exact_mod_cast this
  have hs := size_arith C ((m + 1 : ℕ) : ℝ) r TT.card ((p : ℝ) ^ goodG' r de h x) cStar c0 (2 * r * n' * cpp) Y
    (orbitWindowCount r de h x : ℝ) hC hk1 hrr hNN hQ1 (Nat.cast_nonneg _) (Nat.cast_nonneg _) (by positivity) hY0.le
    (Nat.cast_nonneg _) hN1
  have hsa := le_trans hs h12
  have hkk : ((r + K : ℕ) : ℝ) = ((m + 1 : ℕ) : ℝ) := by rw [hk]
  have hden : 0 < Y * ((r + K : ℕ) : ℝ) ^ 2 := by rw [hkk]; positivity
  have hQ0 : 0 < (p : ℝ) ^ goodG' r de h x := by linarith
  have hfl : ((16 * orbitWindowCount r de h x * c0 : ℕ) : ℤ) ≤ sl p F (flatDeg lam0) Y (r + K) jz xx := by
    unfold sl
    rw [Int.le_floor, le_div_iff₀ hden]
    refine le_trans ?_ hBo
    rw [le_div_iff₀ hQ0, hkk]
    push_cast
    push_cast at hsa
    linarith
  have hfl' : ((16 * orbitWindowCount r de h x * c0 : ℕ) : ℝ) ≤ (sl p F (flatDeg lam0) Y (r + K) jz xx : ℝ) := by
    exact_mod_cast hfl
  push_cast at hfl'
  linarith

theorem restWordBound (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) : RestWordBound D CLa Ck Crk Cdeg :=
  fun _ => ⟨16, by norm_num, fun C hC => wordBoundStep C CLa hC⟩

end Formalism.MainNotions.PairMembershipBlocks
