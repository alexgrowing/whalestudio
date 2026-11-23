import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.GoodPathWeightOfParts
import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.ReflectionMemGlevCastSucc
import Mathlib

noncomputable section

namespace Formalism.MainNotions.SelectionLemmas.Pf.TE

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

section Dict

variable {n' r : ℕ} [NeZero n'] [NeZero r] (F : Frames n' r) (j : ℤ) {L₁ N₁ : ℕ}

omit [NeZero r] in
theorem idx_card (i : Fin (segN F j)) : ((F.letters j).filter (· < segE F j i)).card = i.val := by
  classical
  have hIio : (Finset.univ.filter (· < i) : Finset (Fin (segN F j))) = Finset.Iio i := by
    ext k
    simp
  have hfe : (F.letters j).filter (· < segE F j i) =
      (Finset.univ.filter (· < i)).image
        (fun k : Fin (segN F j) => (((F.letters j).orderIsoOfFin rfl k : {x // x ∈ F.letters j}) : ℤ)) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hx, hlt⟩
      refine ⟨((F.letters j).orderIsoOfFin rfl).symm ⟨x, hx⟩, ?_, by simp⟩
      exact (OrderIso.symm_apply_lt _).mpr hlt
    · rintro ⟨k, hk, rfl⟩
      exact ⟨(((F.letters j).orderIsoOfFin rfl) k).2, ((F.letters j).orderIsoOfFin rfl).strictMono hk⟩
  have hinj : Function.Injective
      (fun k : Fin (segN F j) => (((F.letters j).orderIsoOfFin rfl k : {x // x ∈ F.letters j}) : ℤ)) :=
    fun a b h => (OrderIso.injective _) (Subtype.ext h)
  rw [hfe, Finset.card_image_of_injective _ hinj, hIio, Fin.card_Iio]

variable {F} {j}

omit [NeZero r] in
theorem fr_lt (hV : F.Valid L₁ N₁) (J : ℤ) : ∀ i i', i < i' → i' < r → F.fr J i < F.fr J i' := by
  obtain ⟨_, _, hinc, _⟩ := id hV
  intro i i' h hr
  induction i' with
  | zero => omega
  | succ k ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with h' | h'
    · exact lt_trans (ih h' (by omega)) (hinc J k hr)
    · subst h'
      exact hinc J i hr

omit [NeZero r] in
theorem fr_le (hV : F.Valid L₁ N₁) (J : ℤ) (i i' : ℕ) (h : i ≤ i') (hr : i' < r) : F.fr J i ≤ F.fr J i' := by
  rcases Nat.eq_or_lt_of_le h with rfl | h'
  · exact le_rfl
  · exact le_of_lt (fr_lt hV J i i' h' hr)

omit [NeZero r] in
theorem fr_inj (hV : F.Valid L₁ N₁) (J : ℤ) (i i' : ℕ) (hi : i < r) (hi' : i' < r) (h : F.fr J i = F.fr J i') :
    i = i' := by
  rcases lt_trichotomy i i' with h1 | h1 | h1
  · exact absurd h (ne_of_lt (fr_lt hV J i i' h1 hi'))
  · exact h1
  · exact absurd h (ne_of_gt (fr_lt hV J i' i h1 hi))

theorem fr_prev_lt (hV : F.Valid L₁ N₁) (j : ℤ) : F.fr (j - 1) (r - 1) < F.fr j 0 := by
  obtain ⟨_, _, _, hnext, _⟩ := id hV
  have := hnext (j - 1)
  rwa [sub_add_cancel] at this

theorem frj_mem (hV : F.Valid L₁ N₁) (j : ℤ) (i' : ℕ) (h : i' < r) : F.fr j i' ∈ F.letters j := by
  obtain ⟨_, _, _, _, hTT, _⟩ := id hV
  unfold Frames.letters
  rw [Finset.mem_filter, Finset.mem_Icc]
  refine ⟨⟨?_, fr_le hV j i' (r - 1) (by omega) (by omega)⟩, (hTT j i' h).1⟩
  have h1 := fr_le hV (j - 1) 0 (r - 1) (by omega) (by omega)
  have h2 := fr_prev_lt hV j
  have h3 := fr_le hV j 0 i' (by omega) h
  linarith

theorem frp_mem (hV : F.Valid L₁ N₁) (j : ℤ) (i' : ℕ) (h : i' < r) : F.fr (j - 1) i' ∈ F.letters j := by
  obtain ⟨_, _, _, _, hTT, _⟩ := id hV
  unfold Frames.letters
  rw [Finset.mem_filter, Finset.mem_Icc]
  refine ⟨⟨fr_le hV (j - 1) 0 i' (by omega) h, ?_⟩, (hTT (j - 1) i' h).1⟩
  have h1 := fr_le hV (j - 1) i' (r - 1) (by omega) (by omega)
  have h2 := fr_prev_lt hV j
  have h3 := fr_le hV j 0 (r - 1) (by omega) (by omega)
  linarith

private theorem segE_mem_lemma_6 (J : ℤ) (i : Fin (segN F J)) : segE F J i ∈ F.letters J :=
  ((F.letters J).orderIsoOfFin rfl i).2

private theorem segE_lt_lemma_7 (J : ℤ) {a b : Fin (segN F J)} : segE F J a < segE F J b ↔ a < b := by
  unfold segE
  rw [Subtype.coe_lt_coe]
  exact OrderIso.lt_iff_lt _

private theorem segE_le_lemma_8 (J : ℤ) {a b : Fin (segN F J)} : segE F J a ≤ segE F J b ↔ a ≤ b := by
  unfold segE
  rw [Subtype.coe_le_coe]
  exact OrderIso.le_iff_le _

private theorem segE_surj_lemma_9 (J : ℤ) {x : ℤ} (hx : x ∈ F.letters J) : ∃ k : Fin (segN F J), segE F J k = x :=
  ⟨((F.letters J).orderIsoOfFin rfl).symm ⟨x, hx⟩, by unfold segE; simp⟩

private theorem segE_inj_lemma_10 (J : ℤ) : Function.Injective (segE F J) := by
  intro a b h
  rcases lt_trichotomy a b with h' | h' | h'
  · exact absurd h (ne_of_lt ((segE_lt_lemma_7 J).mpr h'))
  · exact h'
  · exact absurd h (ne_of_gt ((segE_lt_lemma_7 J).mpr h'))

private theorem gap_lemma_2 (hV : F.Valid L₁ N₁) (J : ℤ) : ∀ k, k < r → ∀ x, F.fr J 0 ≤ x → x < F.fr J k →
    posOf n' x ∈ F.TT → ∃ m < k, x = F.fr J m := by
  obtain ⟨_, _, _, _, _, hgap, _⟩ := id hV
  intro k
  induction k with
  | zero =>
    intro _ x h1 h2 _
    exact absurd h2 (not_lt.mpr h1)
  | succ k ih =>
    intro hk x h1 h2 hx
    rcases lt_trichotomy x (F.fr J k) with h3 | h3 | h3
    · obtain ⟨m, hm, hxm⟩ := ih (by omega) x h1 h3 hx
      exact ⟨m, by omega, hxm⟩
    · exact ⟨k, by omega, h3⟩
    · exact absurd hx (hgap J k x hk h3 h2)

private theorem countW_lemma_3 (hV : F.Valid L₁ N₁) (J : ℤ) (i' : ℕ) (hi' : i' < r) :
    ((F.letters J).filter (· < F.fr (J - 1) i')).card = i' := by
  have hfe : (F.letters J).filter (· < F.fr (J - 1) i') = (Finset.range i').image (F.fr (J - 1)) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨hx, hlt⟩
      unfold Frames.letters at hx
      rw [Finset.mem_filter, Finset.mem_Icc] at hx
      obtain ⟨m, hm, hxm⟩ := gap_lemma_2 hV (J - 1) i' hi' x hx.1.1 hlt hx.2
      exact ⟨m, hm, hxm.symm⟩
    · rintro ⟨m, hm, rfl⟩
      exact ⟨frp_mem hV J m (by omega), fr_lt hV (J - 1) m i' hm hi'⟩
  rw [hfe, Finset.card_image_of_injOn, Finset.card_range]
  intro a ha b hb hab
  simp only [Finset.coe_range, Set.mem_Iio] at ha hb
  exact fr_inj hV (J - 1) a b (by omega) (by omega) hab

private theorem countT_lemma_4 (hV : F.Valid L₁ N₁) (J : ℤ) (i' : ℕ) (hi' : i' < r) :
    ((F.letters J).filter (F.fr J i' ≤ ·)).card = r - i' := by
  have hfe : (F.letters J).filter (F.fr J i' ≤ ·) = (Finset.Ico i' r).image (F.fr J) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_Ico]
    constructor
    · rintro ⟨hx, hle⟩
      unfold Frames.letters at hx
      rw [Finset.mem_filter, Finset.mem_Icc] at hx
      rcases lt_or_eq_of_le hx.1.2 with hlt | heq
      · obtain ⟨m, hm, hxm⟩ := gap_lemma_2 hV J (r - 1) (by omega) x
          (le_trans (fr_le hV J 0 i' (Nat.zero_le _) hi') hle) hlt hx.2
        subst hxm
        refine ⟨m, ⟨?_, by omega⟩, rfl⟩
        by_contra hc
        exact absurd hle (not_le.mpr (fr_lt hV J m i' (by omega) hi'))
      · exact ⟨r - 1, ⟨by omega, by omega⟩, heq.symm⟩
    · rintro ⟨m, ⟨hm1, hm2⟩, rfl⟩
      exact ⟨frj_mem hV J m hm2, fr_le hV J i' m hm1 hm2⟩
  rw [hfe, Finset.card_image_of_injOn, Nat.card_Ico]
  intro a ha b hb hab
  simp only [Finset.coe_Ico, Set.mem_Ico] at ha hb
  exact fr_inj hV J a b ha.2 hb.2 hab

private theorem countTlt_lemma_5 (hV : F.Valid L₁ N₁) (J : ℤ) (i' : ℕ) (hi' : i' < r) :
    ((F.letters J).filter (· < F.fr J i')).card + (r - i') = (F.letters J).card := by
  rw [← countT_lemma_4 hV J i' hi']
  have e := Finset.card_sdiff_add_card_eq_card (Finset.filter_subset (F.fr J i' ≤ ·) (F.letters J))
  have hs : (F.letters J) \ (F.letters J).filter (F.fr J i' ≤ ·) = (F.letters J).filter (· < F.fr J i') := by
    ext y
    simp only [Finset.mem_sdiff, Finset.mem_filter]
    constructor
    · rintro ⟨hy, h⟩
      exact ⟨hy, not_le.mp fun h' => h ⟨hy, h'⟩⟩
    · rintro ⟨hy, h⟩
      exact ⟨hy, fun h' => absurd h'.2 (not_le.mpr h)⟩
  rw [hs] at e
  exact e

theorem idx_w (hV : F.Valid L₁ N₁) (i : Fin (segN F j)) (i' : ℕ) (hi' : i' < r) (h : segE F j i = F.fr (j - 1) i') :
    i.val = i' := by
  have h1 := idx_card F j i
  rw [h, countW_lemma_3 hV j i' hi'] at h1
  exact h1.symm

theorem idx_tau (hV : F.Valid L₁ N₁) (i : Fin (segN F j)) (i' : ℕ) (hi' : i' < r) (h : segE F j i = F.fr j i') :
    i.val + (r - i') = segN F j := by
  have h1 := idx_card F j i
  rw [h] at h1
  have h2 := countTlt_lemma_5 hV j i' hi'
  rw [h1] at h2
  exact h2

theorem r_le_segN (hV : F.Valid L₁ N₁) (j : ℤ) : r ≤ segN F j := by
  have hr0 : 0 < r := Nat.pos_of_ne_zero (NeZero.ne r)
  have h1 := countT_lemma_4 hV j 0 hr0
  have h2 := Finset.card_filter_le (F.letters j) (F.fr j 0 ≤ ·)
  rw [h1] at h2
  unfold segN
  omega

theorem dict_tau (hV : F.Valid L₁ N₁) (i : Fin (segN F j)) (i' : Fin r) :
    segE F j i = F.fr j i'.val ↔ i.val = (segN F j - r) + i'.val := by
  have hr := r_le_segN hV j
  have hi' := i'.isLt
  constructor
  · intro h
    have := idx_tau hV i i'.val i'.isLt h
    omega
  · intro h
    obtain ⟨k, hk⟩ := segE_surj_lemma_9 j (frj_mem hV j i'.val i'.isLt)
    have := idx_tau hV k i'.val i'.isLt hk
    have hki : k = i := by
      apply Fin.ext
      omega
    subst hki
    exact hk

theorem dict_early (hV : F.Valid L₁ N₁) (i : Fin (segN F j)) :
    segE F j i < F.fr j 0 ↔ i.val < segN F j - r := by
  have hr0 : 0 < r := Nat.pos_of_ne_zero (NeZero.ne r)
  have hr := r_le_segN hV j
  obtain ⟨k, hk⟩ := segE_surj_lemma_9 j (frj_mem hV j 0 hr0)
  have hkv := (dict_tau hV k ⟨0, hr0⟩).mp hk
  rw [← hk, segE_lt_lemma_7, Fin.lt_iff_val_lt_val, hkv]
  show i.val < segN F j - r + 0 ↔ i.val < segN F j - r
  omega

theorem dict_wE (hV : F.Valid L₁ N₁) (i : Fin (segN F j)) (h : i.val < r) : segE F j i = F.fr (j - 1) i.val := by
  obtain ⟨k, hk⟩ := segE_surj_lemma_9 j (frp_mem hV j i.val h)
  have hki : k = i := Fin.ext (idx_w hV k i.val h hk)
  subst hki
  exact hk

theorem dict_w (hV : F.Valid L₁ N₁) (i : Fin (segN F j)) : F.IsW j (segE F j i) ↔ i.val < r := by
  have hr0 : 0 < r := Nat.pos_of_ne_zero (NeZero.ne r)
  have hr := r_le_segN hV j
  have hw : segE F j ⟨r - 1, by omega⟩ = F.fr (j - 1) (r - 1) :=
    dict_wE hV _ (by show r - 1 < r; omega)
  unfold Frames.IsW
  rw [← hw, segE_le_lemma_8, Fin.le_iff_val_le_val]
  show i.val ≤ r - 1 ↔ i.val < r
  omega

theorem mem_LLset_iff (hV : F.Valid L₁ N₁) (x : ℤ) :
    x ∈ F.LLset j ↔ x ∈ F.letters j ∧ ¬ F.IsW j x ∧ x < F.fr j 0 := by
  have hr0 : 0 < r := Nat.pos_of_ne_zero (NeZero.ne r)
  have h1 := fr_le hV (j - 1) 0 (r - 1) (Nat.zero_le _) (by omega)
  have h2 := fr_le hV j 0 (r - 1) (Nat.zero_le _) (by omega)
  have h3 := fr_prev_lt hV j
  unfold Frames.LLset Frames.letters Frames.IsW
  simp only [Finset.mem_filter, Finset.mem_Ioo, Finset.mem_Icc, not_le]
  constructor
  · rintro ⟨⟨ha, hb⟩, hT⟩
    exact ⟨⟨⟨by linarith, by linarith⟩, hT⟩, ha, hb⟩
  · rintro ⟨⟨_, hT⟩, ha, hb⟩
    exact ⟨⟨ha, hb⟩, hT⟩

theorem dict_LL (hV : F.Valid L₁ N₁) (i : Fin (segN F j)) :
    segE F j i ∈ F.LLset j ↔ r ≤ i.val ∧ i.val < segN F j - r := by
  rw [mem_LLset_iff hV, dict_w hV, dict_early hV]
  have hm := segE_mem_lemma_6 j i
  constructor
  · rintro ⟨_, h1, h2⟩
    exact ⟨not_lt.mp h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨hm, not_lt.mpr h1, h2⟩

theorem LLset_eq_image (hV : F.Valid L₁ N₁) (j : ℤ) :
    F.LLset j = (Finset.univ.filter fun i : Fin (segN F j) => r ≤ i.val ∧ i.val < segN F j - r).image (segE F j) := by
  ext x
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hx
    have hxl := ((mem_LLset_iff hV x).mp hx).1
    obtain ⟨k, rfl⟩ := segE_surj_lemma_9 j hxl
    exact ⟨k, (dict_LL hV k).mp hx, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact (dict_LL hV k).mpr hk

omit [NeZero n'] [NeZero r] in
theorem card_fin_range (N a b : ℕ) (hb : b ≤ N) :
    (Finset.univ.filter fun i : Fin N => a ≤ i.val ∧ i.val < b).card = b - a := by
  have hm : (Finset.univ.filter fun i : Fin N => a ≤ i.val ∧ i.val < b).map Fin.valEmbedding = Finset.Ico a b := by
    ext y
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply,
      Finset.mem_Ico]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact hi
    · intro hy
      exact ⟨⟨y, by omega⟩, hy, rfl⟩
  rw [← Finset.card_map Fin.valEmbedding, hm, Nat.card_Ico]

theorem card_LLset (hV : F.Valid L₁ N₁) (j : ℤ) : (F.LLset j).card = segN F j - r - r := by
  rw [LLset_eq_image hV j, Finset.card_image_of_injective _ (segE_inj_lemma_10 j),
    card_fin_range _ _ _ (Nat.sub_le _ _)]

theorem two_r_le (hV : F.Valid L₁ N₁) (j : ℤ) : 2 * r ≤ segN F j - r := by
  obtain ⟨_, _, _, _, _, _, hLL, _⟩ := id hV
  have h1 := (hLL j).1
  rw [card_LLset hV j] at h1
  omega

theorem card_LLset_le (hV : F.Valid L₁ N₁) (i : Fin (segN F j)) (hi : r ≤ i.val) (hi2 : i.val < segN F j - r) :
    ((F.LLset j).filter (· ≤ segE F j i)).card = i.val + 1 - r := by
  have hiv := i.isLt
  rw [LLset_eq_image hV j]
  have hfe : ((Finset.univ.filter fun k : Fin (segN F j) => r ≤ k.val ∧ k.val < segN F j - r).image
      (segE F j)).filter (· ≤ segE F j i) =
      (Finset.univ.filter fun k : Fin (segN F j) => r ≤ k.val ∧ k.val < i.val + 1).image (segE F j) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨k, hk, rfl⟩, hle⟩
      rw [segE_le_lemma_8, Fin.le_iff_val_le_val] at hle
      exact ⟨k, ⟨hk.1, by omega⟩, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      refine ⟨⟨k, ⟨hk.1, by omega⟩, rfl⟩, ?_⟩
      rw [segE_le_lemma_8, Fin.le_iff_val_le_val]
      omega
  rw [hfe, Finset.card_image_of_injective _ (segE_inj_lemma_10 j), card_fin_range _ _ _ (by omega)]

theorem dict_lateV (hV : F.Valid L₁ N₁) (i : Fin (segN F j)) (h : segN F j - r ≤ i.val + r) : Even (segE F j i) := by
  obtain ⟨_, _, _, _, hTT, _, hLL, _⟩ := id hV
  have hr := r_le_segN hV j
  have h2r := two_r_le hV j
  have hiv := i.isLt
  by_cases hi : segN F j - r ≤ i.val
  · have hi' : i.val - (segN F j - r) < r := by omega
    have he := (dict_tau hV i ⟨i.val - (segN F j - r), hi'⟩).mpr
      (by show i.val = segN F j - r + (i.val - (segN F j - r)); omega)
    rw [he]
    exact (hTT j _ hi').2
  · have hin : segE F j i ∈ F.LLset j := (dict_LL hV i).mpr ⟨by omega, by omega⟩
    have hcnt := card_LLset_le hV i (by omega) (by omega)
    have hcard := card_LLset hV j
    exact (((hLL j).2.1 _ hin) (Or.inr (by rw [hcnt, hcard]; omega))).1

end Dict

end Formalism.MainNotions.SelectionLemmas.Pf.TE
