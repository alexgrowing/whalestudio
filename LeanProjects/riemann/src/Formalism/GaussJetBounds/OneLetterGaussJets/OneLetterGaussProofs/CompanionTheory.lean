import Formalism.GaussJetBounds.OneLetterGaussJets.StatementN
import Formalism.IncomingBounds.WeightIdentities

noncomputable section
open scoped BigOperators

universe u v w

namespace Formalism.DworkPowerSeriesWeights.OddLevelGainBounds

open Formalism.IncomingBounds

lemma gamma_nonneg {l : ℕ} (hl : 3 ≤ l) : 0 ≤ gam l := by
  unfold gam
  have hl' : (3:ℝ) ≤ l := by exact_mod_cast hl
  apply div_nonneg (by linarith)
  nlinarith

lemma inv_le_gamma {l : ℕ} (hl : 3 ≤ l) : 1 / (l : ℝ) ≤ gam l := by
  unfold gam
  have hl' : (3:ℝ) ≤ l := by exact_mod_cast hl
  have h1 : (0:ℝ) < l := by linarith
  have h2 : (0:ℝ) < (l:ℝ) ^ 2 - 1 := by nlinarith
  first
  | (rw [div_le_div_iff₀ h1 h2]; nlinarith)
  | (rw [div_le_div_iff h1 h2]; nlinarith)

lemma two_gamma_le_three_div {l : ℕ} (hl : 3 ≤ l) : 2 * gam l ≤ 3 / (l : ℝ) := by
  unfold gam
  have hl' : (3:ℝ) ≤ l := by exact_mod_cast hl
  have h1 : (0:ℝ) < l := by linarith
  have h2 : (0:ℝ) < (l:ℝ) ^ 2 - 1 := by nlinarith
  rw [mul_div_assoc']
  first
  | (rw [div_le_div_iff₀ h2 h1]; nlinarith)
  | (rw [div_le_div_iff h2 h1]; nlinarith)

theorem proposition_six : PropSix7 := by
  intro l d inst hl hd hev TT k D w E hk hw hE hoff hon
  classical
  have hA := lemmaFa
  have hc := lemmaFc
  have hI := incomingBound
  have hl3 : (3:ℝ) ≤ l := by exact_mod_cast hl
  have hl0 : (0:ℝ) < l := by linarith
  have hk3 : (3:ℝ) ≤ k := by exact_mod_cast hk
  have hg := gamma_nonneg hl
  obtain ⟨S, hS⟩ : ∃ S : ℝ, S = ∑ s : ZMod d, w s := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = ∑ s ∈ TT, w s := ⟨_, rfl⟩
  have hS0 : 0 ≤ S := by rw [hS]; exact Finset.sum_nonneg (fun s _ => (hw s).le)
  have hTS : T ≤ S := by
    rw [hS, hT]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun s _ _ => (hw s).le)
  obtain ⟨Ws, hWs⟩ : ∃ f : ZMod d → ℝ, f = fun s => ((k:ℝ) - 1) * w s := ⟨_, rfl⟩
  obtain ⟨E', hE'⟩ : ∃ f : ZMod d → ℝ, f = fun s => if s ∈ TT then 2 * w s else 0 := ⟨_, rfl⟩
  have hWsapp : ∀ s, Ws s = ((k:ℝ) - 1) * w s := fun s => by rw [hWs]
  rw [← hS, ← hT, ← hWs]
  have hD0 : 0 ≤ D := fun s => by
    show (0:ℝ) ≤ D s
    have h1 := hw s
    have h2 := (hE s).1
    by_cases hs : s ∈ TT
    · rw [hon s hs]; nlinarith
    · rw [hoff s hs]; nlinarith
  have hE'0 : 0 ≤ E' := fun s => by
    show (0:ℝ) ≤ E' s
    rw [hE']
    try dsimp only
    split_ifs
    · linarith [hw s]
    · exact le_rfl
  have hDE : D + E' = Ws + E := by
    funext s
    simp only [Pi.add_apply, hE', hWs]
    by_cases hs : s ∈ TT
    · rw [if_pos hs, hon s hs]; ring
    · rw [if_neg hs, hoff s hs]; ring

  obtain ⟨⟨sD, hsD, -, hFsD⟩, -⟩ := hA l d hl hd hev D hD0
  have h2 := (hc l d hl hd hev D E' sD hD0 hE'0 ⟨hsD, hFsD⟩).2
  rw [hDE] at h2
  have hE'sum : ∑ s, E' s = 2 * T := by
    rw [hT, Finset.mul_sum, hE', ← Finset.sum_filter]
    simp
  rw [hE'sum] at h2

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
  have hgl := inv_le_gamma hl
  have hpt : ∀ s, E s * max (sW s - gam l) 0 ≤
      4 * w s / l + 4 * (if 2 / (l:ℝ) ≤ sW s then w s else 0) := by
    intro s
    obtain ⟨hE0, hE4⟩ := hE s
    have hs0 := (hsW.1 s).1
    have hs1 := (hsW.1 s).2
    have hws := hw s
    have hm0 : 0 ≤ max (sW s - gam l) 0 := le_max_right _ _
    have hq : 0 ≤ 4 * w s / l := by positivity
    split_ifs with hcase
    · have hm : max (sW s - gam l) 0 ≤ 1 := max_le (by linarith) zero_le_one
      calc E s * max (sW s - gam l) 0 ≤ E s * 1 := mul_le_mul_of_nonneg_left hm hE0
        _ ≤ 4 * w s := by linarith
        _ ≤ _ := by linarith
    · push Not at hcase
      have h21 : 2 / (l:ℝ) = 1 / l + 1 / l := by ring
      have hm : max (sW s - gam l) 0 ≤ 1 / l := max_le (by linarith) (by positivity)
      calc E s * max (sW s - gam l) 0 ≤ (4 * w s) * (1 / l) :=
            mul_le_mul hE4 hm hm0 (by linarith)
        _ = 4 * w s / l + 4 * 0 := by ring
  have hsum3 : ∑ s, E s * max (sW s - gam l) 0 ≤ 8 / l * S := by
    calc ∑ s, E s * max (sW s - gam l) 0
        ≤ ∑ s, (4 * w s / l + 4 * (if 2 / (l:ℝ) ≤ sW s then w s else 0)) :=
          Finset.sum_le_sum (fun s _ => hpt s)
      _ = 4 * S / l + 4 * ∑ s ∈ Finset.univ.filter (fun s : ZMod d => 2 / (l : ℝ) ≤ sW s), w s := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_filter, ← Finset.sum_div,
            ← Finset.mul_sum, ← hS]
      _ ≤ 4 * S / l + 4 * (S / l) := by linarith
      _ = 8 / l * S := by ring
  constructor
  · have : gam l * (2 * T) = 2 * gam l * T := by ring
    linarith
  · have h2g := two_gamma_le_three_div hl
    have hT' : 2 * gam l * T ≤ 3 / l * S :=
      calc 2 * gam l * T ≤ 2 * gam l * S := mul_le_mul_of_nonneg_left hTS (by linarith)
        _ ≤ 3 / l * S := mul_le_mul_of_nonneg_right h2g hS0
    have h11 : 11 / (l:ℝ) * S = 3 / l * S + 8 / l * S := by ring
    linarith

lemma tsum_le_of_dominated {f g b : ℕ → ℝ} (hg0 : ∀ e, 0 ≤ g e) (hgf : ∀ e, g e ≤ f e)
    (hfb : ∀ e, f e ≤ b e) (hb : Summable b) : ∑' e, g e ≤ ∑' e, f e := by
  have hf : Summable f := Summable.of_nonneg_of_le (fun e => (hg0 e).trans (hgf e)) hfb hb
  have hg : Summable g := Summable.of_nonneg_of_le hg0 (fun e => (hgf e).trans (hfb e)) hb
  first
  | exact Summable.tsum_le_tsum hgf hg hf
  | exact tsum_le_tsum hgf hg hf

lemma least_odd_top_level_spec {d : ℕ} [NeZero d] (TT : Finset (ZMod d)) (s : ZMod d) (e : ℕ)
    (h : dTop d TT s = (e : ℕ∞)) :
    (Odd e ∧ s + (e : ZMod d) ∈ TT) ∧ ∀ e' : ℕ, Odd e' → s + (e' : ZMod d) ∈ TT → e ≤ e' := by
  classical
  have hex : ∃ e' : ℕ, Odd e' ∧ s + (e' : ZMod d) ∈ TT := by
    by_contra hne
    push_neg at hne
    have htop : dTop d TT s = ⊤ := by
      unfold dTop
      simp only [iInf_eq_top]
      intro e' he'
      exact absurd he'.2 (hne e' he'.1)
    rw [htop] at h
    first
    | exact ENat.top_ne_coe e h
    | simp at h
  have hle : ∀ e' : ℕ, Odd e' → s + (e' : ZMod d) ∈ TT → dTop d TT s ≤ (e' : ℕ∞) := by
    intro e' h1 h2
    unfold dTop
    exact iInf₂_le e' ⟨h1, h2⟩
  have hfind : dTop d TT s = ((Nat.find hex : ℕ) : ℕ∞) := by
    apply le_antisymm
    · exact hle _ (Nat.find_spec hex).1 (Nat.find_spec hex).2
    · unfold dTop
      apply le_iInf₂
      intro e' he'
      exact_mod_cast Nat.find_min' hex he'
  have he : e = Nat.find hex := by
    rw [h] at hfind
    exact_mod_cast hfind
  refine ⟨?_, ?_⟩
  · rw [he]
    exact Nat.find_spec hex
  · intro e' h1 h2
    have h3 := hle e' h1 h2
    rw [h] at h3
    exact_mod_cast h3

theorem gain_ge_inner_sum : GainDominatesInnerSum := by
  intro l d inst hl TT nu1 nu2 s
  classical
  have hl2 : (2:ℝ) ≤ l := by exact_mod_cast hl
  have hl0 : (0:ℝ) < l := by linarith
  have hb : Summable (fun e : ℕ => (nu1 s : ℝ) / (l:ℝ) ^ e) := by
    have : Summable (fun e : ℕ => ((l:ℝ)⁻¹) ^ e) :=
      summable_geometric_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ (by linarith))
    simpa [div_eq_mul_inv, inv_pow] using this.mul_left (nu1 s : ℝ)
  unfold topTerm oddLevelGainSum
  refine tsum_le_of_dominated (b := fun e : ℕ => (nu1 s : ℝ) / (l:ℝ) ^ e) ?_ ?_ ?_ hb
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
    · obtain ⟨⟨-, hmem⟩, hmin⟩ := least_odd_top_level_spec TT s e heq.symm
      have hP : ∃ s' ∈ TT, IsLeast {e' : ℕ | Odd e' ∧ s + (e' : ZMod d) = s'} e :=
        ⟨s + (e : ZMod d), hmem, ⟨ho, rfl⟩, fun e' he' => hmin e' he'.1 (he'.2 ▸ hmem)⟩
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

end Formalism.DworkPowerSeriesWeights.OddLevelGainBounds
