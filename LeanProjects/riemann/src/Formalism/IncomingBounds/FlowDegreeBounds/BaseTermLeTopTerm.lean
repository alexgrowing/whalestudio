import Formalism.IncomingBounds.IncomingBound
import Formalism.IncomingBounds.LevelTail

noncomputable section
open scoped BigOperators

namespace Formalism.IncomingBounds

lemma cor_gam_nonneg {l : ℕ} (hl : 3 ≤ l) : 0 ≤ gam l := by
  unfold gam
  have : (3:ℝ) ≤ l := by exact_mod_cast hl
  apply div_nonneg <;> nlinarith

lemma cor_gam_le {l : ℕ} (hl : 3 ≤ l) : gam l ≤ 9 / (8 * l) := by
  unfold gam
  have h3 : (3:ℝ) ≤ l := by exact_mod_cast hl
  rw [div_le_div_iff₀ (by nlinarith) (by nlinarith)]
  nlinarith

lemma cor_tsum_cmp {f g b : ℕ → ℝ} (hg0 : ∀ e, 0 ≤ g e) (hgf : ∀ e, g e ≤ f e)
    (hfb : ∀ e, f e ≤ b e) (hb : Summable b) : ∑' e, g e ≤ ∑' e, f e := by
  have hf : Summable f := Summable.of_nonneg_of_le (fun e => (hg0 e).trans (hgf e)) hfb hb
  have hg : Summable g := Summable.of_nonneg_of_le hg0 hgf hf
  exact hg.tsum_le_tsum hgf hf

lemma baseTerm_le_topTerm (l d : ℕ) [NeZero d] (hl : 3 ≤ l) (TT : Finset (ZMod d))
    (nu1 nu2 : ZMod d → ℕ) (s : ZMod d) :
    baseTerm l d TT nu1 nu2 s ≤ topTerm l d TT nu1 nu2 s := by
  classical
  have hl3 : (3:ℝ) ≤ l := by exact_mod_cast hl
  have hl0 : (0:ℝ) < l := by linarith
  have hb : Summable (fun e : ℕ => (nu1 s : ℝ) / (l:ℝ) ^ e) := by
    have : Summable (fun e : ℕ => ((l:ℝ)⁻¹) ^ e) :=
      summable_geometric_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ (by linarith))
    simpa [div_eq_mul_inv, inv_pow] using this.mul_left (nu1 s : ℝ)
  unfold topTerm baseTerm
  refine cor_tsum_cmp (b := fun e : ℕ => (nu1 s : ℝ) / (l:ℝ) ^ e) ?_ ?_ ?_ hb
  · intro e
    try dsimp only
    split_ifs
    · exact le_max_right _ _
    · exact le_rfl
  · intro e
    try dsimp only
    have hcap : (0:ℝ) ≤ capL d TT nu1 nu2 (s + (e : ZMod d)) := Nat.cast_nonneg _
    have hpe : (0:ℝ) < (l:ℝ) ^ e := pow_pos hl0 e
    have hn2 : (0:ℝ) ≤ (nu2 s : ℝ) / (l:ℝ) ^ e := div_nonneg (Nat.cast_nonneg _) hpe.le
    have hA' : (0:ℝ) ≤ (nu1 s : ℝ) / (l:ℝ) ^ e := div_nonneg (Nat.cast_nonneg _) hpe.le
    have hsub : ((nu1 s : ℝ) - nu2 s) / (l:ℝ) ^ e =
        (nu1 s : ℝ) / (l:ℝ) ^ e - (nu2 s : ℝ) / (l:ℝ) ^ e := sub_div _ _ _
    by_cases ho : Odd e
    swap
    · simp [ho]
    rcases lt_trichotomy (e : ℕ∞) (dTop d TT s) with hlt | heq | hgt
    · rw [if_pos (show Odd e ∧ (e : ℕ∞) < dTop d TT s from ⟨ho, hlt⟩)]
      split_ifs
      · apply max_le_max _ le_rfl
        rw [hsub]; linarith
      · exact le_max_right _ _
    · have hP : ∃ e0 : ℕ, dTop d TT s = (e0 : ℕ∞) ∧ s + (e : ZMod d) = s + (e0 : ZMod d) :=
        ⟨e, heq.symm, rfl⟩
      rw [if_neg (show ¬ (Odd e ∧ (e : ℕ∞) < dTop d TT s) from fun h => (lt_irrefl _ (heq ▸ h.2))),
        if_neg (show ¬ (Odd e ∧ dTop d TT s < (e : ℕ∞)) from fun h => (lt_irrefl _ (heq ▸ h.2)))]
      split_ifs with h
      · exact absurd hP h.2
      · exact le_rfl
    · rw [if_neg (show ¬ (Odd e ∧ (e : ℕ∞) < dTop d TT s) from fun h => (not_lt.mpr hgt.le h.2)),
        if_pos (show Odd e ∧ dTop d TT s < (e : ℕ∞) from ⟨ho, hgt⟩)]
      split_ifs
      · exact max_le (by rw [hsub]; linarith) hA'
      · exact hA'
  · intro e
    try dsimp only
    have hcap : (0:ℝ) ≤ capL d TT nu1 nu2 (s + (e : ZMod d)) := Nat.cast_nonneg _
    have hpe : (0:ℝ) < (l:ℝ) ^ e := pow_pos hl0 e
    have hA' : (0:ℝ) ≤ (nu1 s : ℝ) / (l:ℝ) ^ e := div_nonneg (Nat.cast_nonneg _) hpe.le
    split_ifs
    · exact max_le (by linarith) hA'
    · exact le_rfl
    · exact hA'

theorem corFromThmA_of (hF : FlowAttained) (hA : LemmaFa) (hc : LemmaFc) (hI : IncomingBound) :
    CorFromThmA := by
  refine ⟨15, ?_⟩
  intro l d inst hl hd hev TT nu1 nu2 size N0 N1 a k c CA vK w E h21 h12 hk hw hE hoff hon hcap hThm
  classical
  have hl3 : (3:ℝ) ≤ l := by exact_mod_cast hl
  have hl0 : (0:ℝ) < l := by linarith
  have hk3 : (3:ℝ) ≤ k := by exact_mod_cast hk
  have hg := cor_gam_nonneg hl
  obtain ⟨S, hS⟩ : ∃ S : ℝ, S = ∑ s : ZMod d, w s := ⟨_, rfl⟩
  have hS0 : 0 ≤ S := by rw [hS]; exact Finset.sum_nonneg (fun s _ => (hw s).le)
  obtain ⟨Ws, hWs⟩ : ∃ f : ZMod d → ℝ, f = fun s => ((k:ℝ) - 1) * w s := ⟨_, rfl⟩
  obtain ⟨Dr, hDr⟩ : ∃ f : ZMod d → ℝ, f = fun s => (Dl d TT nu1 size s : ℝ) := ⟨_, rfl⟩
  obtain ⟨E', hE'⟩ : ∃ f : ZMod d → ℝ, f = fun s => if s ∈ TT then 2 * w s else 0 := ⟨_, rfl⟩
  have hWsapp : ∀ s, Ws s = ((k:ℝ) - 1) * w s := fun s => by rw [hWs]
  have hDr0 : 0 ≤ Dr := fun s => by show (0:ℝ) ≤ Dr s; rw [hDr]; exact Nat.cast_nonneg _
  have hE'0 : 0 ≤ E' := fun s => by
    show (0:ℝ) ≤ E' s
    rw [hE']
    try dsimp only
    split_ifs
    · linarith [hw s]
    · exact le_rfl
  have hDE : Dr + E' = Ws + E := by
    funext s
    simp only [Pi.add_apply, hDr, hE', hWs]
    by_cases hs : s ∈ TT
    · rw [if_pos hs, hon s hs]; ring
    · rw [if_neg hs, hoff s hs]; ring

  obtain ⟨⟨sD, hsD, -, hFsD⟩, -⟩ := hA l d hl hd hev Dr hDr0
  have h2 := (hc l d hl hd hev Dr E' sD hDr0 hE'0 ⟨hsD, hFsD⟩).2
  rw [hDE] at h2
  have hE'sum : ∑ s, E' s ≤ 2 * S := by
    rw [hS, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro s _
    rw [hE']
    dsimp only
    split_ifs <;> linarith [hw s]

  have hWs0 : 0 ≤ Ws := fun s => by
    show (0:ℝ) ≤ Ws s
    rw [hWsapp]
    have := hw s
    have : (0:ℝ) ≤ (k:ℝ) - 1 := by linarith
    positivity
  obtain ⟨⟨sW, hsW, -, hFsW⟩, -⟩ := hA l d hl hd hev Ws hWs0
  have hoptW : IsOptDual l d Ws sW := ⟨hsW, hFsW⟩
  have h3 := (hc l d hl hd hev Ws E sW hWs0 (fun s => (hE s).1) hoptW).1
  have hinc := hI l d hl hd hev Ws sW hWs0 hoptW
  have hfilt : ∑ s ∈ Finset.univ.filter (fun s : ZMod d => 2 / (l : ℝ) ≤ sW s), w s ≤ S / l := by
    have e1 : ∑ s ∈ Finset.univ.filter (fun s : ZMod d => 2 / (l : ℝ) ≤ sW s), Ws s =
        ((k:ℝ) - 1) * ∑ s ∈ Finset.univ.filter (fun s : ZMod d => 2 / (l : ℝ) ≤ sW s), w s := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun s _ => hWsapp s)
    have e2 : ∑ s, Ws s = ((k:ℝ) - 1) * S := by
      rw [hS, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun s _ => hWsapp s)
    rw [e1, e2, mul_div_assoc] at hinc
    have hk1 : 0 < (k:ℝ) - 1 := by linarith
    exact le_of_mul_le_mul_left hinc hk1
  have hpt : ∀ s, E s * max (sW s - gam l) 0 ≤
      8 * w s / l + 4 * (if 2 / (l:ℝ) ≤ sW s then w s else 0) := by
    intro s
    obtain ⟨hE0, hE4⟩ := hE s
    have hs0 := (hsW.1 s).1
    have hs1 := (hsW.1 s).2
    have hws := hw s
    have hm0 : 0 ≤ max (sW s - gam l) 0 := le_max_right _ _
    have hq : 0 ≤ 8 * w s / l := by positivity
    split_ifs with hcase
    · have hm : max (sW s - gam l) 0 ≤ 1 := max_le (by linarith) zero_le_one
      calc E s * max (sW s - gam l) 0 ≤ E s * 1 := mul_le_mul_of_nonneg_left hm hE0
        _ ≤ 4 * w s := by linarith
        _ ≤ _ := by linarith
    · push Not at hcase
      have hm : max (sW s - gam l) 0 ≤ 2 / l := max_le (by linarith) (by positivity)
      calc E s * max (sW s - gam l) 0 ≤ (4 * w s) * (2 / l) :=
            mul_le_mul hE4 hm hm0 (by linarith)
        _ = 8 * w s / l + 4 * 0 := by ring
  have hsum3 : ∑ s, E s * max (sW s - gam l) 0 ≤ 12 * S / l := by
    calc ∑ s, E s * max (sW s - gam l) 0
        ≤ ∑ s, (8 * w s / l + 4 * (if 2 / (l:ℝ) ≤ sW s then w s else 0)) :=
          Finset.sum_le_sum (fun s _ => hpt s)
      _ = 8 * S / l + 4 * ∑ s ∈ Finset.univ.filter (fun s : ZMod d => 2 / (l : ℝ) ≤ sW s), w s := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_filter, ← Finset.sum_div,
            ← Finset.mul_sum, ← hS]
      _ ≤ 8 * S / l + 4 * (S / l) := by linarith
      _ = 12 * S / l := by ring

  have hgE : gam l * ∑ s, E' s ≤ 9 / 4 * S / l := by
    have hl' : (l:ℝ) ≠ 0 := ne_of_gt hl0
    calc gam l * ∑ s, E' s ≤ gam l * (2 * S) := mul_le_mul_of_nonneg_left hE'sum hg
      _ ≤ 9 / (8 * l) * (2 * S) := mul_le_mul_of_nonneg_right (cor_gam_le hl) (by linarith)
      _ = 9 / 4 * S / l := by field_simp; ring

  have h1 : ∑ s ∈ TT, baseTerm l d TT nu1 nu2 s ≤ ∑ s ∈ TT, topTerm l d TT nu1 nu2 s :=
    Finset.sum_le_sum (fun s _ => baseTerm_le_topTerm l d hl TT nu1 nu2 s)

  unfold ThmABound at hThm
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← hDr] at hThm
  rw [← hS, ← hWs]
  have hfin : 12 * S / l + 9 / 4 * S / l ≤ 15 * S / l := by
    rw [← add_div, div_le_div_iff_of_pos_right hl0]
    linarith
  linarith

theorem contentShift_of (hF : FlowAttained) (hA : LemmaFa) (hc : LemmaFc) (hI : IncomingBound) :
    ContentShift := by
  intro l d inst hl hd hev th D' E hth hD' hE hED
  classical
  obtain ⟨⟨sig, hsig, -, hFsig⟩, -⟩ := hA l d hl hd hev D' hD'
  have hopt : IsOptDual l d D' sig := ⟨hsig, hFsig⟩
  have h1 := (hc l d hl hd hev D' E sig hD' hE hopt).1
  have hinc := hI l d hl hd hev D' sig hD' hopt
  have hl3 : (3:ℝ) ≤ l := by exact_mod_cast hl
  have hl0 : (0:ℝ) < l := by linarith
  have hg := cor_gam_nonneg hl
  have hpt : ∀ a, E a * max (sig a - gam l) 0 ≤
      4 * th * D' a / l + 2 * th * (if 2 / (l:ℝ) ≤ sig a then D' a else 0) := by
    intro a
    have hs0 := (hsig.1 a).1
    have hs1 := (hsig.1 a).2
    have hEa := hE a
    have hDa := hD' a
    have hEDa := hED a
    have hm : max (sig a - gam l) 0 ≤ sig a := max_le (by linarith) hs0
    have hm0 : 0 ≤ max (sig a - gam l) 0 := le_max_right _ _
    have hq : 0 ≤ 4 * th * D' a / l := div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hth) hDa) hl0.le
    split_ifs with hcase
    · calc E a * max (sig a - gam l) 0 ≤ E a * 1 := mul_le_mul_of_nonneg_left (hm.trans hs1) hEa
        _ ≤ 2 * th * D' a := by linarith
        _ ≤ _ := by linarith
    · push Not at hcase
      calc E a * max (sig a - gam l) 0 ≤ (2 * th * D' a) * (2 / l) :=
            mul_le_mul hEDa (hm.trans hcase.le) hm0 (mul_nonneg (mul_nonneg (by norm_num) hth) hDa)
        _ = 4 * th * D' a / l + 2 * th * 0 := by ring
  have hsum : ∑ a, E a * max (sig a - gam l) 0 ≤ 6 * th * (∑ a, D' a) / l := by
    calc ∑ a, E a * max (sig a - gam l) 0
        ≤ ∑ a, (4 * th * D' a / l + 2 * th * (if 2 / (l:ℝ) ≤ sig a then D' a else 0)) :=
          Finset.sum_le_sum (fun a _ => hpt a)
      _ = 4 * th * (∑ a, D' a) / l +
            2 * th * ∑ a ∈ Finset.univ.filter (fun s : ZMod d => 2 / (l : ℝ) ≤ sig s), D' a := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_filter, ← Finset.sum_div,
            ← Finset.mul_sum]
      _ ≤ 4 * th * (∑ a, D' a) / l + 2 * th * ((∑ a, D' a) / l) := by
          have : 0 ≤ 2 * th := by linarith
          nlinarith
      _ = 6 * th * (∑ a, D' a) / l := by ring
  linarith

end Formalism.IncomingBounds
