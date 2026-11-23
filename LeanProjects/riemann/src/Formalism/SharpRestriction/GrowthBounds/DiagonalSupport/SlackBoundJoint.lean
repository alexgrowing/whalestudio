import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.SlackBoundReal

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.Proposition5Numerics

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords
open Formalism.MainNotions.G.WittFrameLocaliserOrders Formalism.MainNotions.G.symbolGeneratorData

section Geo

variable {n' r : ℕ} [NeZero n'] {Fr : Frames n' r} {TT : Finset (Fin n')} {L₁ L₂ N₁ G' : ℕ}

theorem LL_sub_letters (hV : Fr.Valid L₁ N₁) (hr : 1 ≤ r) (j y : ℤ) (hy : y ∈ Fr.LLset j) :
    y ∈ Fr.letters j ∧ ¬ Fr.IsW j y := by
  simp only [Frames.LLset, Finset.mem_filter, Finset.mem_Ioo] at hy
  obtain ⟨⟨h1, h2⟩, hT⟩ := hy
  have hr0 : r - 1 < r := by omega
  have a1 := fr_le_last hV (j - 1) (show 0 < r by omega)
  have a2 := fr_le_last hV j (show 0 < r by omega)
  refine ⟨?_, ?_⟩
  · simp only [Frames.letters, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨by omega, by omega⟩, hT⟩
  · simp only [Frames.IsW]
    omega

theorem LL_gap (hF : FramesOK TT L₁ L₂ N₁ G' Fr) (hr : 1 ≤ r) (j y : ℤ) (hy : y ∈ Fr.LLset j) :
    y + L₂ < Fr.fr j 0 := by
  have hV := hF.2.1
  have hG := hF.2.2.2.2 j
  obtain ⟨hyl, -⟩ := LL_sub_letters hV hr j y hy
  have hylt : y < Fr.fr j 0 := by
    simp only [Frames.LLset, Finset.mem_filter, Finset.mem_Ioo] at hy
    exact hy.1.2
  set S := (Fr.letters j).filter (fun z => z < Fr.fr j 0) with hS
  have hyS : y ∈ S := Finset.mem_filter.mpr ⟨hyl, hylt⟩
  have hne : S.Nonempty := ⟨y, hyS⟩
  have hm := Finset.max'_mem S hne
  rw [Finset.mem_filter] at hm
  have key := hG (S.max' hne) hm.1 hm.2 (fun z hz hzl => Finset.le_max' S z (Finset.mem_filter.mpr ⟨hz, hzl⟩))
  have := Finset.le_max' S y hyS
  omega

theorem Bo_ge (hV : Fr.Valid L₁ N₁) (hr : 1 ≤ r) (p : ℕ) (hp : 1 ≤ p) (deg : Fin n' → ℕ) (a : ℝ)
    (hdeg : ∀ s ∈ Fr.TT, a ≤ (deg s : ℝ)) (j x : ℤ) (hx : x ∈ Fr.letters j) (hW : ¬ Fr.IsW j x) :
    a / (p : ℝ) ^ (Fr.fr j (r - 1) - Fr.fr (j - 1) 0).toNat ≤ Bo p Fr deg j x := by
  have ho := Formalism.MainNotions.G.WittFrameLocaliserOrders.oldest_mem_segment_letters Fr L₁ N₁ hV hr j x hx hW
  set o := Fr.oldest j x with ho_def
  have hoL := ho
  simp only [Frames.letters, Finset.mem_filter, Finset.mem_Icc] at hoL
  obtain ⟨⟨ho1, ho2⟩, hoT⟩ := hoL
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  have hdle : Fr.dist j o ≤ (Fr.fr j (r - 1) - Fr.fr (j - 1) 0).toNat := by
    simp only [Frames.dist]
    omega
  have hpow : (p : ℝ) ^ Fr.dist j o ≤ (p : ℝ) ^ (Fr.fr j (r - 1) - Fr.fr (j - 1) 0).toNat :=
    pow_le_pow_right₀ hpR hdle
  have hpos1 : (0 : ℝ) < (p : ℝ) ^ Fr.dist j o := pow_pos hp0 _
  have hpos2 : (0 : ℝ) < (p : ℝ) ^ (Fr.fr j (r - 1) - Fr.fr (j - 1) 0).toNat := pow_pos hp0 _
  have had : a ≤ (deg (posOf n' o) : ℝ) := hdeg _ hoT
  show a / _ ≤ levDeg p Fr deg j o
  simp only [levDeg]
  rcases le_or_gt a 0 with ha | ha
  · have h1 : a / (p : ℝ) ^ (Fr.fr j (r - 1) - Fr.fr (j - 1) 0).toNat ≤ 0 := div_nonpos_of_nonpos_of_nonneg ha hpos2.le
    have h2 : (0 : ℝ) ≤ (deg (posOf n' o) : ℝ) / (p : ℝ) ^ Fr.dist j o := by positivity
    linarith
  · calc a / (p : ℝ) ^ (Fr.fr j (r - 1) - Fr.fr (j - 1) 0).toNat ≤ a / (p : ℝ) ^ Fr.dist j o :=
          div_le_div_of_nonneg_left ha.le hpos1 hpow
      _ ≤ _ := div_le_div_of_nonneg_right had hpos1.le

end Geo

section Shift

variable {n' r : ℕ} [NeZero n'] {Fr : Frames n' r} {L₁ N₁ : ℕ} {J : ℕ} [NeZero J]

theorem seg_shift (hV : Fr.Valid L₁ N₁) (hJ : J = Fr.J) (j : ZMod J) :
    ∃ s : ℤ, ∀ i, Fr.fr (segZ j + 1) i = Fr.fr (segZ (j + 1)) i + s ∧ Fr.fr (segZ j) i = Fr.fr (segZ (j + 1) - 1) i + s := by
  have hJ1 := hV.2.1
  subst hJ
  have hJpos : 0 < Fr.J := Nat.pos_of_ne_zero (NeZero.ne _)
  have hv : (j + 1).val = (j.val + 1) % Fr.J := by
    rw [ZMod.val_add, ZMod.val_one_eq_one_mod]
    rcases Nat.lt_or_ge 1 Fr.J with h | h
    · rw [Nat.mod_eq_of_lt h]
    · have : Fr.J = 1 := by omega
      simp [this]
  have hjl : j.val < Fr.J := ZMod.val_lt j
  simp only [segZ]
  rcases Nat.lt_or_ge (j.val + 1) Fr.J with h | h
  · refine ⟨0, fun i => ?_⟩
    rw [hv, Nat.mod_eq_of_lt h]
    push_cast
    simp
  · have hj : j.val + 1 = Fr.J := by omega
    have h0 : (j + 1).val = 0 := by rw [hv, hj, Nat.mod_self]
    refine ⟨(n' : ℤ), fun i => ?_⟩
    rw [h0]
    have e1 : ((j.val : ℕ) : ℤ) + 1 = ((0 : ℕ) : ℤ) + (Fr.J : ℤ) := by push_cast; omega
    have e2 : ((j.val : ℕ) : ℤ) = ((0 : ℕ) : ℤ) - 1 + (Fr.J : ℤ) := by push_cast; omega
    constructor
    · rw [e1, hJ1]
    · rw [e2, hJ1]

end Shift

section HypH

variable {n' r : ℕ} [NeZero n'] {Fr : Frames n' r} {TT : Finset (Fin n')} {L₁ L₂ N₁ G' : ℕ}
  {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {J : ℕ} [NeZero J]

theorem dLL_le (hF : FramesOK TT L₁ L₂ N₁ G' Fr) (hr : 1 ≤ r) (hp : 3 ≤ p) (hL : L₁ ≤ L₂) (Dt : SignedChainData p O r J)
    (hnL : ∀ j, Dt.nL j = (Fr.LLset (segZ j)).card) (a : ℝ) (ha : 0 ≤ a)
    (hd : ∀ x, (lowP Fr p x : ℝ) * (Dt.d x : ℝ) ≤ 2 * a) (j : ZMod J) :
    (Dt.dLL j : ℝ) ≤ 3 * a * (p : ℝ) ^ (-((Fr.dist (segZ j) (Fr.fr (segZ j) 0) : ℕ) : ℤ) - L₁ - 1) := by
  have hV := hF.2.1
  have hr' : 0 < r := by omega
  set jj := segZ j with hjj
  set D := Fr.dist jj (Fr.fr jj 0) with hD
  have hpR : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  set q : ℝ := (p : ℝ)⁻¹ with hq
  have hq0 : 0 ≤ q := inv_nonneg.mpr hp0.le
  have hq1 : q < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have hq3 : q ≤ 1 / 3 := by
    rw [hq, one_div]
    exact inv_anti₀ (by norm_num) hpR
  let e : Fin (Dt.nL j) → ℕ := fun l => Fr.dist jj (llPos Fr jj l)
  have hmem : ∀ l : Fin (Dt.nL j), llPos Fr jj l ∈ Fr.LLset jj := fun l =>
    Formalism.MainNotions.Proposition5Numerics.llPos_mem Fr jj l (by rw [← hnL j]; exact l.isLt)
  have a0 := fr_le_last hV jj hr'
  have he : ∀ l : Fin (Dt.nL j), ((e l : ℕ) : ℤ) = Fr.fr jj (r - 1) - llPos Fr jj l := by
    intro l
    have hy := hmem l
    rw [Formalism.MainNotions.Proposition5Numerics.mem_LLset] at hy
    simp only [e, Frames.dist]
    omega
  have hDe : (D : ℤ) = Fr.fr jj (r - 1) - Fr.fr jj 0 := by
    simp only [hD, Frames.dist]
    omega
  have hM : ∀ l : Fin (Dt.nL j), D + L₂ + 1 ≤ e l := by
    intro l
    have h2 := LL_gap hF hr jj _ (hmem l)
    have := he l
    omega
  have hinj : Function.Injective e := by
    intro l l' hll
    have h1 := he l
    have h2 := he l'
    rw [hll] at h1
    have : llPos Fr jj l = llPos Fr jj l' := by omega
    exact Fin.ext (Formalism.MainNotions.Proposition5Numerics.llPos_inj Fr jj l l'
      (by rw [← hnL j]; exact l.isLt) (by rw [← hnL j]; exact l'.isLt) this)
  have hterm : ∀ l : Fin (Dt.nL j), (Dt.d ⟨j, Sum.inl l⟩ : ℝ) ≤ 2 * a * q ^ (e l) := by
    intro l
    have h := hd ⟨j, Sum.inl l⟩
    have hl : (lowP Fr p (⟨j, Sum.inl l⟩ : TL J Dt.nL r) : ℝ) = (p : ℝ) ^ (e l) := by
      simp only [lowP, posTL, e, jj]
      push_cast
      rfl
    rw [hl] at h
    have hpe : (0 : ℝ) < (p : ℝ) ^ (e l) := pow_pos hp0 _
    rw [hq, inv_pow, ← div_eq_mul_inv, le_div_iff₀ hpe]
    linarith
  have hsum : (Dt.dLL j : ℝ) ≤ 2 * a * ∑ k ∈ Finset.univ.image e, q ^ k := by
    simp only [SignedChainData.dLL]
    push_cast
    rw [Finset.sum_image (fun x _ y _ h => hinj h), Finset.mul_sum]
    exact Finset.sum_le_sum (fun l _ => hterm l)
  set S := Finset.univ.image e
  set N := S.sup id + 1
  have hsub : S ⊆ Finset.Ico (D + L₂ + 1) N := by
    intro k hk
    rw [Finset.mem_Ico]
    obtain ⟨l, -, rfl⟩ := Finset.mem_image.mp hk
    refine ⟨hM l, ?_⟩
    have := Finset.le_sup (f := id) hk
    simp only [id] at this
    omega
  have hgeo : ∑ k ∈ S, q ^ k ≤ q ^ (D + L₂ + 1) / (1 - q) :=
    (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => pow_nonneg hq0 _)).trans
      (geom_sum_Ico_le_of_lt_one hq0 hq1)
  have hz : (p : ℝ) ^ (-((D : ℕ) : ℤ) - L₁ - 1) = q ^ (D + L₁ + 1) := by
    rw [show (-((D : ℕ) : ℤ) - L₁ - 1) = -(((D + L₁ + 1 : ℕ)) : ℤ) by push_cast; ring]
    rw [zpow_neg, zpow_natCast, hq, inv_pow]
  rw [hz]
  have hqq : q ^ (D + L₂ + 1) ≤ q ^ (D + L₁ + 1) := pow_le_pow_of_le_one hq0 hq1.le (by omega)
  have h1q : 0 < 1 - q := by linarith
  have hfrac : q ^ (D + L₂ + 1) / (1 - q) ≤ 3 / 2 * q ^ (D + L₁ + 1) := by
    rw [div_le_iff₀ h1q]
    have hqn : 0 ≤ q ^ (D + L₁ + 1) := pow_nonneg hq0 _
    nlinarith
  calc (Dt.dLL j : ℝ) ≤ 2 * a * ∑ k ∈ S, q ^ k := hsum
    _ ≤ 2 * a * (3 / 2 * q ^ (D + L₁ + 1)) := by
        apply mul_le_mul_of_nonneg_left (hgeo.trans hfrac)
        linarith
    _ = 3 * a * q ^ (D + L₁ + 1) := by ring

theorem slack_bound_real (r : ℕ) (x c s : ℝ) (h1 : x ≤ s / 8) (h2 : 100 * (r : ℝ) ^ 2 * c ≤ s) (hr : 2 ≤ r) (hc : 0 ≤ c) :
    x + 26 * (r : ℝ) * c ≤ 3 / 8 * s := by
  have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have h3 : 26 * (r : ℝ) * c ≤ 25 * (r : ℝ) ^ 2 * c := by
    have : 26 * (r : ℝ) ≤ 25 * (r : ℝ) ^ 2 := by nlinarith
    nlinarith
  nlinarith

end HypH

section HypH2

variable {n' r : ℕ} [NeZero n'] {Fr : Frames n' r} {TT : Finset (Fin n')} {L₁ L₂ N₁ G' : ℕ}
  {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {J : ℕ} [NeZero J]

theorem posU_mem (hV : Fr.Valid L₁ N₁) (hr : 1 ≤ r) (j : ℤ) (u : ℕ) (hu : u ≤ (Fr.LLset j).card) :
    posU Fr (Fr.LLset j).card j u ∈ Fr.letters j ∧ ¬ Fr.IsW j (posU Fr (Fr.LLset j).card j u) := by
  unfold posU
  split_ifs with hlt
  · exact LL_sub_letters hV hr j _ (Formalism.MainNotions.Proposition5Numerics.llPos_mem Fr j u hlt)
  · have hu' : u - (Fr.LLset j).card = 0 := by omega
    rw [hu']
    have hV' := hV
    obtain ⟨-, -, -, h4, h5, -⟩ := hV'
    have a1 := fr_le_last hV (j - 1) (show 0 < r by omega)
    have a2 := fr_le_last hV j (show 0 < r by omega)
    have a3 := h4 (j - 1)
    simp only [sub_add_cancel] at a3
    refine ⟨?_, ?_⟩
    · simp only [Frames.letters, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨by omega, a2⟩, (h5 j 0 (by omega)).1⟩
    · simp only [Frames.IsW]
      omega

theorem slack_bound_joint (hF : FramesOK TT L₁ L₂ N₁ G' Fr) (hr : 2 ≤ r) (hp : 3 ≤ p) (hL : L₁ ≤ L₂) (deg : Fin n' → ℕ) (Y : ℝ)
    (k mS : ℕ) (K : ℕ) [NeZero K] (Dt : SignedChainData p O r J) (dPl : TL J Dt.nL r → ℕ) (ka : ZMod J → ℕ → Fin K → ℤ)
    (hT : Tied Fr p deg Y k mS K Dt dPl ka) (cPr : ℝ) (hc : Dt.c = cPr) (hc0 : 0 ≤ cPr)
    (hsl : ∀ j (i : Fin (Dt.nch j)), Dt.sl j i = 3 / 8 * slU Fr p deg Y k Dt.nL j i.val)
    (a : ℝ) (ha : 0 ≤ a) (hdeg : ∀ s ∈ Fr.TT, a ≤ (deg s : ℝ))
    (hd : ∀ x, (lowP Fr p x : ℝ) * (Dt.d x : ℝ) ≤ 2 * a)
    (hII5 : ∀ (Dd : ℕ) (Qj dj B : ℝ), (p : ℝ) ^ Dd ≤ Formalism.CountingSumsFrames.QII p G' → 1 ≤ Qj → Qj ≤ Formalism.CountingSumsFrames.QII p G' →
      dj ≤ 3 * a * (p : ℝ) ^ (-(Dd : ℤ) - L₁ - 1) → a / ((p : ℝ) ^ Dd * Qj) ≤ B →
      r * dj / Qj ≤ 3 * r * (p : ℝ) ^ (-(L₁ : ℤ) - 1) * B ∧
        3 * r * (p : ℝ) ^ (-(L₁ : ℤ) - 1) * B ≤ Formalism.CountingSumsFrames.slII Y k B / 8)
    (hII0 : ∀ B : ℝ, a / Formalism.CountingSumsFrames.QII p G' ≤ B → 100 * (r : ℝ) ^ 2 * cPr ≤ Formalism.CountingSumsFrames.slII Y k B) :
    Dt.Hyp 26 := by
  have hV := hF.2.1
  have hG := hF.2.2.1
  have hr1 : 1 ≤ r := by omega
  have hnL := hT.2.1
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast (show 1 ≤ p by omega)
  have hp0 : (0 : ℝ) < p := by linarith
  intro j m i
  obtain ⟨s, hs⟩ := seg_shift hV hT.1 j
  have hsl' : Dt.sl (j + 1) i = 3 / 8 * slU Fr p deg Y k Dt.nL (j + 1) i.val := hsl (j + 1) i
  have hi0 := i.isLt
  have hnch := hT.2.2.2.2.2.1 (j + 1)
  have hnL1 := hnL (j + 1)
  have hgP := hT.2.2.2.2.1 j m
  set jj := segZ j with hjj
  set jj' := segZ (j + 1) with hjj'
  have a0 := fr_le_last hV jj (show 0 < r by omega)
  have a1 := fr_le_last hV (jj + 1) (show 0 < r by omega)
  have a2 := hV.2.2.2.1 jj
  have b0 := fr_le_last hV jj' (show 0 < r by omega)
  have b1 := fr_le_last hV (jj' - 1) (show 0 < r by omega)
  have b2 := hV.2.2.2.1 (jj' - 1)
  simp only [sub_add_cancel] at b2
  set Dd := Fr.dist jj (Fr.fr jj 0) with hDd
  set g := (Fr.fr (jj + 1) (r - 1) - Fr.fr jj (r - 1)).toNat with hg
  set E := (Fr.fr jj' (r - 1) - Fr.fr (jj' - 1) 0).toNat with hE
  have hDdz : (Dd : ℤ) = Fr.fr jj (r - 1) - Fr.fr jj 0 := by
    simp only [hDd, Frames.dist]; omega
  have hgz : (g : ℤ) = Fr.fr (jj + 1) (r - 1) - Fr.fr jj (r - 1) := by simp only [hg]; omega
  have hEz : (E : ℤ) = Fr.fr jj' (r - 1) - Fr.fr (jj' - 1) 0 := by simp only [hE]; omega
  have hEq : Dd + g = E := by
    have e1 := (hs (r - 1)).1
    have e2 := (hs 0).2
    omega
  have hDdG : Dd ≤ G' := by
    have := hG jj
    have := fr_le_last hV (jj - 1) (show 0 < r by omega)
    have := hV.2.2.2.1 (jj - 1)
    simp only [sub_add_cancel] at this
    omega
  have hgG : g ≤ G' := by
    have := hG (jj + 1)
    simp only [add_sub_cancel_right] at this
    omega
  have hEG : E ≤ G' := by
    have := hG jj'
    omega
  have hP : (Dt.P j m : ℝ) = (p : ℝ) ^ g := by
    simp only [SignedChainData.P]
    rw [hgP]
    push_cast
    rfl
  have hi : i.val ≤ (Fr.LLset jj').card := by omega
  obtain ⟨hxl, hxW⟩ := posU_mem hV hr1 jj' i.val hi
  set x := posU Fr (Fr.LLset jj').card jj' i.val with hx
  set B := Bo p Fr deg jj' x with hB
  have hBge : a / (p : ℝ) ^ E ≤ B := Bo_ge hV hr1 p (by omega) deg a hdeg jj' x hxl hxW
  have hslB : Dt.sl (j + 1) i = 3 / 8 * Formalism.CountingSumsFrames.slII Y k B := by
    rw [hsl']
    congr 1
    simp only [slU]
    rw [hnL1]
    rfl
  have hQII : Formalism.CountingSumsFrames.QII p G' = (p : ℝ) ^ G' := rfl
  have hDdQ : (p : ℝ) ^ Dd ≤ Formalism.CountingSumsFrames.QII p G' := by rw [hQII]; exact pow_le_pow_right₀ hpR hDdG
  have hQ1 : 1 ≤ (p : ℝ) ^ g := one_le_pow₀ hpR
  have hQQ : (p : ℝ) ^ g ≤ Formalism.CountingSumsFrames.QII p G' := by rw [hQII]; exact pow_le_pow_right₀ hpR hgG
  have hdj := dLL_le hF hr1 hp hL Dt hnL a ha hd j
  have hB5 : a / ((p : ℝ) ^ Dd * (p : ℝ) ^ g) ≤ B := by
    rw [← pow_add, hEq]; exact hBge
  obtain ⟨h5a, h5b⟩ := hII5 Dd ((p : ℝ) ^ g) (Dt.dLL j) B hDdQ hQ1 hQQ hdj hB5
  have hB0 : a / Formalism.CountingSumsFrames.QII p G' ≤ B := by
    refine le_trans ?_ hBge
    rw [hQII]
    exact div_le_div_of_nonneg_left ha (pow_pos hp0 _) (pow_le_pow_right₀ hpR hEG)
  have h0 := hII0 B hB0
  show (r : ℝ) * (Dt.dLL j : ℝ) / (Dt.P j m : ℝ) + 26 * (r : ℝ) * Dt.c ≤ Dt.sl (j + 1) i
  rw [hslB, hc, hP]
  have key := slack_bound_real r ((r : ℝ) * (Dt.dLL j : ℝ) / (p : ℝ) ^ g) cPr (Formalism.CountingSumsFrames.slII Y k B)
    (h5a.trans h5b) h0 hr hc0
  linarith

end HypH2

end Formalism.MainNotions.Proposition5Numerics
