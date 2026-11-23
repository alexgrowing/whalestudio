import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.TriangularCountLeSq

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.Proposition5Numerics

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords
open Formalism.MainNotions.G.WittFrameLocaliserOrders Formalism.MainNotions.G.symbolGeneratorData

theorem le_cube_mul (k N : ℝ) (hk : 1 ≤ k) (hN : 1 ≤ N) : k ≤ k ^ 3 * N := by
  have hk2 : 1 ≤ k ^ 2 := by nlinarith
  have h1 : k ≤ k ^ 3 := by nlinarith
  calc k ≤ k ^ 3 := h1
    _ = k ^ 3 * 1 := (mul_one _).symm
    _ ≤ k ^ 3 * N := mul_le_mul_of_nonneg_left hN (by positivity)

theorem k_le_a {C : ℝ} (hC1 : 1 ≤ C) {p n' m r : ℕ} {TT : Finset (Fin n')} {L₁ L₂ : ℕ} {de h x : ℝ}
    {lam0 : Fin n' → Fin (m + 1) → ℤ} {aT bT : Fin n' → ℤ} {a Y : ℝ} {cpp c0 Dp cStar : ℕ}
    (H : Hyps C p n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar) : ((m + 1 : ℕ) : ℝ) ≤ a := by
  have hB := hyps_basic hC1 H
  obtain ⟨h1, h2, _, _, _, _, _, _, _, _, h11, h12⟩ := H
  have hr1 : 1 ≤ r := by omega
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (by omega : 1 ≤ p)
  have hk1 : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ m + 1)
  have hN1 : (1 : ℝ) ≤ (TT.card : ℝ) := by exact_mod_cast hB.N_pos
  have hrr : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
  have hQ1 : (1 : ℝ) ≤ (p : ℝ) ^ goodG' r de h x := one_le_pow₀ hp1
  have hcc : (1 : ℝ) ≤ (cStar : ℝ) + ((r : ℝ) * TT.card * c0 + 2 * r * n' * cpp) := by
    have h8' : (1 : ℝ) ≤ (cStar : ℝ) := by exact_mod_cast (by omega : 1 ≤ cStar)
    have : (0 : ℝ) ≤ (r : ℝ) * TT.card * c0 + 2 * r * n' * cpp := by positivity
    linarith
  obtain ⟨z1, _, _⟩ := factor_le_product_seven C (((m + 1 : ℕ) : ℝ) ^ 3) ((r : ℝ) ^ 2) (TT.card : ℝ)
    (((p : ℝ) ^ goodG' r de h x) ^ 5) ((cStar : ℝ) + ((r : ℝ) * TT.card * c0 + 2 * r * n' * cpp)) Y hC1
    (one_le_pow₀ hk1) (one_le_pow₀ hrr) hN1 (one_le_pow₀ hQ1) hcc (by linarith [hB.two_le_Y])
  exact le_trans (le_cube_mul _ _ hk1 hN1) (le_trans z1 h12)

section Geo

variable {n' r : ℕ} [NeZero n'] {Fr : Frames n' r} {L₁ N₁ : ℕ}

theorem posU_mem' (hV : Fr.Valid L₁ N₁) (hr : 1 ≤ r) (j : ℤ) (u : ℕ) (hu : u < (Fr.LLset j).card + r) :
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

theorem sl_lt_Bo (hV : Fr.Valid L₁ N₁) (hr : 1 ≤ r) (p : ℕ) (hp : 1 ≤ p) (deg : Fin n' → ℕ) (a : ℝ) (ha : 0 < a)
    (hdeg : ∀ s ∈ Fr.TT, a ≤ (deg s : ℝ)) (Y : ℝ) (k : ℕ) (hY : 2 ≤ Y) (hk : 1 ≤ k) {J : ℕ} (nL : ZMod J → ℕ)
    (hnL : ∀ j, nL j = (Fr.LLset (segZ j)).card) (j : ZMod J) (u : ℕ) (hu : u < nL j + r) :
    3 / 8 * slU Fr p deg Y k nL j u < Bo p Fr deg (segZ j) (posU Fr (nL j) (segZ j) u) / 2 := by
  have hu' : u < (Fr.LLset (segZ j)).card + r := by rw [← hnL j]; exact hu
  obtain ⟨hx1, hx2⟩ := posU_mem' hV hr (segZ j) u hu'
  rw [← hnL j] at hx1 hx2
  have hB := Bo_ge hV hr p hp deg a hdeg (segZ j) _ hx1 hx2
  have hp' : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
  have hpos : 0 < Bo p Fr deg (segZ j) (posU Fr (nL j) (segZ j) u) := lt_of_lt_of_le (by positivity) hB
  unfold slU
  exact sl_lt_real _ Y (k : ℝ) _ rfl hpos hY (by exact_mod_cast hk)

end Geo

section At

variable {p n' m r K : ℕ} [NeZero n'] [NeZero r] [NeZero K] {TT : Finset (Fin n')} {L₁ L₂ N₁ G' : ℕ} {F : Frames n' r}
  {lam0 : Fin n' → Fin (m + 1) → ℤ} {a : ℝ}

theorem sizeAt_of [hpF : Fact p.Prime] (hk : m + 1 = r + K) (hF : FramesOK TT L₁ L₂ N₁ G' F) (hr : 1 ≤ r)
    (hnb : NB p m r TT.card a) (hka : ((m + 1 : ℕ) : ℝ) ≤ a)
    (hfd : ∀ s ∈ TT, a ≤ (flatDeg lam0 s : ℝ) ∧ (flatDeg lam0 s : ℝ) ≤ 2 * a)
    {J : ℕ} [NeZero J] (nL : ZMod J → ℕ) (hJ : J = F.J) (hnL : ∀ j, nL j = (F.LLset (segZ j)).card) :
    SizeAt (K := K) p F nL (dT TT lam0) (9 * ((TT.card : ℝ) * ((m + 1 : ℕ) : ℝ) ^ 2 * Real.logb p a)) := by
  have hV := hF.2.1
  have hp2 : 2 ≤ p := hpF.out.two_le
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 1 < p)
  have ha2 := hnb.two_le_a
  intro rho dPl dNo hBk bp bn hbp hbn
  have hsum : ∀ x, ((dPl x + dNo x : ℕ) : ℝ) ≤ 2 * a := by
    intro x
    have htop : posOf n' (posTL F x) ∈ TT := by
      have := (posTL_seg F hV hr hnL x).2.2
      rwa [hF.1] at this
    have e := hBk.2 x
    have e2 : dT TT lam0 (posOf n' (posTL F x)) = flatDeg lam0 (posOf n' (posTL F x)) := by
      unfold dT; rw [if_pos htop]
    rw [e2] at e
    have hl : 1 ≤ lowP F p x := Nat.one_le_pow _ _ (by omega)
    have e3 : dPl x + dNo x ≤ flatDeg lam0 (posOf n' (posTL F x)) := by
      have := Nat.mul_le_mul_right (dPl x + dNo x) hl
      omega
    have e4 : ((dPl x + dNo x : ℕ) : ℝ) ≤ (flatDeg lam0 (posOf n' (posTL F x)) : ℝ) := by exact_mod_cast e3
    have := (hfd _ htop).2
    linarith
  have hdp : ∀ x, (dPl x : ℝ) ≤ 2 * a := by
    intro x
    have := hsum x
    push_cast at this
    have h0 : (0 : ℝ) ≤ (dNo x : ℝ) := Nat.cast_nonneg _
    linarith
  have hdn : ∀ x, (dNo x : ℝ) ≤ 2 * a := by
    intro x
    have := hsum x
    push_cast at this
    have h0 : (0 : ℝ) ≤ (dPl x : ℝ) := Nat.cast_nonneg _
    linarith
  have hcard : Fintype.card (TL J nL r) ≤ TT.card := by
    have := card_TL_le F hV hr hJ hnL
    rwa [hF.1] at this
  have A := DnoOf_le (K := K) p hp2 nL dNo TT.card (m + 1) a hr (by omega) hcard hdn ha2 hnb.fourN hka
  have B := mult_level_real p dPl bp hbp TT.card a ha2 hcard hdp
  have Cc := mult_level_real p dNo bn hbn TT.card a ha2 hcard hdn
  have hrk : (r : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : r ≤ m + 1)
  have hKk : (K : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : K ≤ m + 1)
  have hk1 : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ m + 1)
  exact size_fin (TT.card : ℝ) ((m + 1 : ℕ) : ℝ) (r : ℝ) (K : ℝ) (Real.logb p a) _ _ _ (Nat.cast_nonneg _)
    (by linarith [hnb.one_le_log]) hk1 (Nat.cast_nonneg _) (Nat.cast_nonneg _) hrk hKk A B Cc

end At

end Formalism.MainNotions.Proposition5Numerics
