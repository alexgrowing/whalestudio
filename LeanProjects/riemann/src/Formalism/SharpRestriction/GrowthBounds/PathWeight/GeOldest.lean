import Formalism.SharpRestriction.GrowthBounds.PathWeight.GeneratorImageIsSymbol

noncomputable section

open Finset Classical

namespace Formalism.MainNotions.G.symbolGeneratorData

open Formalism.MainNotions.G Formalism.MainNotions.SourceCleaning Formalism.MainNotions.G.WittFrameLocaliserOrders

theorem ge_sort (s : Finset ℤ) (i : ℕ) (hi : i < s.card) (d o : ℤ) (ho : o = (s.sort (· ≤ ·)).getD i d) :
    o ∈ s ∧ ∀ T : Finset ℤ, (∀ t, t ∈ T ↔ t ∈ s ∧ o < t) → T.card = s.card - 1 - i := by
  have hlen : i < (s.sort (· ≤ ·)).length := by rw [Finset.length_sort]; exact hi
  rw [List.getD_eq_getElem _ _ hlen] at ho
  have he : (s.sort (· ≤ ·))[i] = s.orderEmbOfFin rfl ⟨i, hi⟩ := (Finset.orderEmbOfFin_apply s rfl ⟨i, hi⟩).symm
  rw [he] at ho
  subst ho
  refine ⟨Finset.orderEmbOfFin_mem _ _ _, fun T hT => ?_⟩
  have h : T = (Finset.Ioi (⟨i, hi⟩ : Fin s.card)).map (s.orderEmbOfFin rfl).toEmbedding := by
    ext t
    rw [hT]
    simp only [mem_map, mem_Ioi, RelEmbedding.coe_toEmbedding]
    constructor
    · rintro ⟨ht, hlt⟩
      have h1 : t ∈ Set.range (s.orderEmbOfFin rfl) := by rw [Finset.range_orderEmbOfFin]; exact ht
      obtain ⟨i', rfl⟩ := h1
      exact ⟨i', (s.orderEmbOfFin rfl).lt_iff_lt.1 hlt, rfl⟩
    · rintro ⟨i', hi', rfl⟩
      exact ⟨Finset.orderEmbOfFin_mem _ _ _, (s.orderEmbOfFin rfl).lt_iff_lt.2 hi'⟩
  rw [h, Finset.card_map, Fin.card_Ioi]

section Count

variable {n' r : ℕ} [NeZero n'] (F : Frames n' r)

def geN (x y : ℤ) : ℕ := ((Finset.Ioo y x).filter fun t => posOf n' t ∈ F.TT ∧ Even t).card

theorem ge_N_lt {x y1 y2 : ℤ} (h12 : y1 < y2) (h2 : y2 < x) (hT : posOf n' y2 ∈ F.TT) (hE : Even y2) :
    geN F x y2 < geN F x y1 := by
  unfold geN
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · exact ⟨y2, by simp only [mem_filter, mem_Ioo]; exact ⟨⟨h12, h2⟩, hT, hE⟩, by simp⟩
  · intro t ht
    simp only [mem_filter, mem_Ioo] at ht ⊢
    exact ⟨⟨by omega, ht.1.2⟩, ht.2⟩

theorem ge_N_inj {x y1 y2 : ℤ} (h1 : y1 < x) (h2 : y2 < x) (hT1 : posOf n' y1 ∈ F.TT) (hE1 : Even y1)
    (hT2 : posOf n' y2 ∈ F.TT) (hE2 : Even y2) (h : geN F x y1 = geN F x y2) : y1 = y2 := by
  rcases lt_trichotomy y1 y2 with h' | h' | h'
  · have := ge_N_lt F h' h2 hT2 hE2; omega
  · exact h'
  · have := ge_N_lt F h' h1 hT1 hE1; omega

theorem ge_Arow (L₁ N₁ : ℕ) (hV : F.Valid L₁ N₁) (hn : Even n') (hr : 1 ≤ r) (x : ℤ) (l : ℕ) (hl : l < r) :
    geN F x (Arow F x l) = l := by
  have hOK := window_holds_even_tops n' r F L₁ N₁ hV hn hr x l hl
  have hlow := bk_Arow_low F x l
  have hlen : l < (evensBefore F x).length := by
    by_contra h
    have h1 : Arow F x l = x := by unfold Arow; exact List.getD_eq_default _ _ (not_lt.1 h)
    have := hOK.2.2
    omega
  obtain ⟨s, hs, hmem⟩ : ∃ s : Finset ℤ, evensBefore F x = (s.sort (· ≤ ·)).reverse ∧
      ∀ t, t ∈ s ↔ (x - (r : ℤ) * n' ≤ t ∧ t < x) ∧ posOf n' t ∈ F.TT ∧ Even t :=
    ⟨_, rfl, fun t => by rw [Finset.mem_filter, Finset.mem_Ico]⟩
  have hcard : l < s.card := by rw [hs, List.length_reverse, Finset.length_sort] at hlen; exact hlen
  have hA : Arow F x l = (s.sort (· ≤ ·)).getD (s.card - 1 - l) 0 := by
    unfold Arow
    rw [List.getD_eq_getElem _ _ hlen, List.getD_eq_getElem _ _ (by rw [Finset.length_sort]; omega)]
    simp only [hs, List.getElem_reverse, Finset.length_sort]
  obtain ⟨_, h2⟩ := ge_sort s (s.card - 1 - l) (by omega) 0 _ hA
  unfold geN
  rw [h2 _ (fun t => by
    simp only [mem_filter, mem_Ioo]
    rw [hmem]
    constructor
    · rintro ⟨⟨a, b⟩, c⟩; exact ⟨⟨⟨by omega, b⟩, c⟩, a⟩
    · rintro ⟨⟨⟨_, b⟩, c⟩, a⟩; exact ⟨⟨a, b⟩, c⟩)]
  omega

theorem ge_oldest (L₁ N₁ : ℕ) (hV : F.Valid L₁ N₁) (hr : 1 ≤ r) (j x : ℤ) (hx : x ∈ F.letters j)
    (hW : ¬ F.IsW j x) :
    (F.oldest j x ∈ F.letters j ∧ Even (F.oldest j x) ∧ F.oldest j x < x) ∧ geN F x (F.oldest j x) = r - 1 := by
  have hc := bd_vectors_before F hr hV.2.2.1 hV.2.2.2.1 hV.2.2.2.2.1 j x hW
  have ho : F.oldest j x = (((F.letters j).filter fun z => Even z ∧ z < x).sort (· ≤ ·)).getD
      (((F.letters j).filter fun z => Even z ∧ z < x).card - r) 0 := by
    unfold Frames.oldest
    simp only [Finset.length_sort]
  obtain ⟨h1, h2⟩ := ge_sort _ _ (by omega) 0 _ ho
  rw [Finset.mem_filter] at h1
  refine ⟨h1, ?_⟩
  unfold geN
  have hx' := hx
  have h1' := h1.1
  unfold Frames.letters at hx' h1'
  rw [Finset.mem_filter, Finset.mem_Icc] at hx' h1'
  rw [h2 _ (fun t => by
    simp only [mem_filter, mem_Ioo]
    unfold Frames.letters
    simp only [mem_filter, mem_Icc]
    constructor
    · rintro ⟨⟨a, b⟩, c, d⟩; exact ⟨⟨⟨⟨by omega, by omega⟩, c⟩, d, b⟩, a⟩
    · rintro ⟨⟨⟨_, c⟩, d, b⟩, a⟩; exact ⟨⟨a, b⟩, c, d⟩)]
  omega

theorem ge_frame (L₁ N₁ : ℕ) (hV : F.Valid L₁ N₁) (j t : ℤ) (ht : posOf n' t ∈ F.TT) (h0 : F.fr j 0 ≤ t) :
    ∀ i, i < r → t ≤ F.fr j i → ∃ i' ≤ i, t = F.fr j i' := by
  intro i
  induction i with
  | zero => intro _ h; exact ⟨0, le_rfl, by omega⟩
  | succ i ih =>
    intro hi h
    by_cases h1 : t ≤ F.fr j i
    · obtain ⟨i', a, b⟩ := ih (by omega) h1
      exact ⟨i', by omega, b⟩
    · by_cases h2 : t = F.fr j (i + 1)
      · exact ⟨i + 1, le_rfl, h2⟩
      · exact absurd ht (hV.2.2.2.2.2.1 j i t hi (by omega) (by omega))

theorem ge_older (L₁ N₁ : ℕ) (hV : F.Valid L₁ N₁) (hn : Even n') (hr : 1 ≤ r) (j x : ℤ) (hx : x ∈ F.letters j)
    (hW : ¬ F.IsW j x) (y : ℤ) (hy : y ∈ F.letters j) (hE : Even y) (hyx : y < x)
    (hA : ∀ l < r, y ≠ Arow F x l) : y < F.oldest j x ∧ (F.IsW j y ∨ y ∈ F.LLset j) := by
  have hy' := hy
  have hx' := hx
  unfold Frames.letters at hy' hx'
  rw [Finset.mem_filter, Finset.mem_Icc] at hy' hx'
  have hN : r ≤ geN F x y := by
    by_contra h
    have hl : geN F x y < r := by omega
    have hOK := window_holds_even_tops n' r F L₁ N₁ hV hn hr x _ hl
    exact hA _ hl (ge_N_inj F hyx hOK.2.2 hy'.2 hE hOK.2.1 hOK.1 (ge_Arow F L₁ N₁ hV hn hr x _ hl).symm)
  obtain ⟨⟨ho1, ho2, ho3⟩, ho4⟩ := ge_oldest F L₁ N₁ hV hr j x hx hW
  refine ⟨?_, ?_⟩
  · by_contra h
    rcases eq_or_lt_of_le (not_lt.1 h) with h' | h'
    · rw [← h'] at hN; omega
    · have := ge_N_lt F h' hyx hy'.2 hE; omega
  · by_cases h0 : y < F.fr j 0
    · by_cases h1 : y ≤ F.fr (j - 1) (r - 1)
      · exact Or.inl h1
      · right
        unfold Frames.LLset
        rw [Finset.mem_filter, Finset.mem_Ioo]
        exact ⟨⟨by omega, h0⟩, hy'.2⟩
    · exfalso
      have hsub : ((Finset.Ioo y x).filter fun t => posOf n' t ∈ F.TT ∧ Even t) ⊆
          (Finset.range (r - 1)).image (fun i => F.fr j i) := by
        intro t ht
        simp only [mem_filter, mem_Ioo] at ht
        obtain ⟨i', hi', rfl⟩ := ge_frame F L₁ N₁ hV j t ht.2.1 (by omega) (r - 1) (by omega) (by omega)
        rw [Finset.mem_image]
        refine ⟨i', ?_, rfl⟩
        rw [Finset.mem_range]
        by_contra hc
        have : i' = r - 1 := by omega
        rw [this] at ht
        omega
      have h2 := Finset.card_le_card hsub
      have h3 := Finset.card_image_le (s := Finset.range (r - 1)) (f := fun i => F.fr j i)
      rw [Finset.card_range] at h3
      unfold geN at hN
      omega

end Count

theorem restGeom : RestGeom := by
  intro p n' r _ F L₁ N₁ hp hr hn hV deg a hdeg j dd hdd x hx
  have hx1 : x ∈ F.letters j := (Finset.mem_filter.1 hx).1
  have hW : ¬ F.IsW j x := (Finset.mem_filter.1 hx).2
  obtain ⟨⟨ho1, ho2, ho3⟩, _⟩ := ge_oldest F L₁ N₁ hV (by omega) j x hx1 hW
  have ho1' := ho1
  unfold Frames.letters at ho1'
  rw [Finset.mem_filter, Finset.mem_Icc] at ho1'
  have hp0 : (0 : ℝ) < p := by
    have : (13 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  have hY : ∀ y ∈ (F.letters j).filter (fun y => Even y ∧ y < x ∧ ∀ l < r, y ≠ Arow F x l),
      y < F.oldest j x ∧ Even y ∧ y ∈ F.letters j ∧ (F.IsW j y ∨ y ∈ F.LLset j) := by
    intro y hy
    rw [Finset.mem_filter] at hy
    obtain ⟨h1, h2, h3, h4⟩ := hy
    obtain ⟨h5, h6⟩ := ge_older F L₁ N₁ hV hn (by omega) j x hx1 hW y h1 h2 h3 h4
    exact ⟨h5, h2, h1, h6⟩
  have hlev : ∀ y ∈ F.letters j, levDeg p F deg j y ≤ 2 * ((a : ℝ) / (p : ℝ) ^ (F.dist j y)) := by
    intro y hy
    unfold Frames.letters at hy
    rw [Finset.mem_filter] at hy
    unfold levDeg
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right (hdeg _ hy.2).2 (pow_pos hp0 _).le
  have hdd' : ∀ y ∈ (F.letters j).filter (fun y => Even y ∧ y < x ∧ ∀ l < r, y ≠ Arow F x l),
      (dd y : ℝ) ≤ 2.02 * ((a : ℝ) / (p : ℝ) ^ (F.dist j y)) := by
    intro y hy
    obtain ⟨_, _, h3, h4⟩ := hY y hy
    have h5 := (abs_le.1 (hdd y h3 h4)).2
    have h6 := hlev y h3
    linarith
  rw [Nat.cast_sum]
  by_cases ha : a = 0
  · have hz : ∀ y ∈ (F.letters j).filter (fun y => Even y ∧ y < x ∧ ∀ l < r, y ≠ Arow F x l),
        (dd y : ℝ) = 0 := by
      intro y hy
      have h1 := hdd' y hy
      rw [ha] at h1
      simp only [Nat.cast_zero, zero_div, mul_zero] at h1
      exact le_antisymm h1 (Nat.cast_nonneg _)
    rw [Finset.sum_eq_zero hz]
    have := level_degree_nonneg p F deg j x
    linarith
  · have hf : ∀ y ∈ (F.letters j).filter (fun y => Even y ∧ y < x ∧ ∀ l < r, y ≠ Arow F x l),
        ((((F.oldest j x - y) / 2).toNat : ℕ) : ℤ) * 2 = F.oldest j x - y ∧ 1 ≤ ((F.oldest j x - y) / 2).toNat := by
      intro y hy
      obtain ⟨h1, h2, _, _⟩ := hY y hy
      obtain ⟨k, hk⟩ := ho2.sub h2
      constructor <;> omega
    have hsum : ∑ y ∈ (F.letters j).filter (fun y => Even y ∧ y < x ∧ ∀ l < r, y ≠ Arow F x l), (dd y : ℝ) =
        ∑ m ∈ ((F.letters j).filter (fun y => Even y ∧ y < x ∧ ∀ l < r, y ≠ Arow F x l)).image
          (fun y => ((F.oldest j x - y) / 2).toNat), (dd (F.oldest j x - 2 * (m : ℤ)) : ℝ) := by
      rw [Finset.sum_image]
      · refine Finset.sum_congr rfl fun y hy => ?_
        have h1 := (hf y hy).1
        have h2 : F.oldest j x - 2 * ((((F.oldest j x - y) / 2).toNat : ℕ) : ℤ) = y := by omega
        rw [h2]
      · intro y1 hy1 y2 hy2 h
        have h1 := (hf y1 hy1).1
        have h2 := (hf y2 hy2).1
        have h' : ((F.oldest j x - y1) / 2).toNat = ((F.oldest j x - y2) / 2).toNat := h
        rw [h'] at h1
        omega
    rw [hsum]
    have hB : (a : ℝ) / (p : ℝ) ^ (F.dist j (F.oldest j x)) ≤ Bo p F deg j x := by
      unfold Bo levDeg
      exact div_le_div_of_nonneg_right (hdeg _ ho1'.2).1 (pow_pos hp0 _).le
    obtain ⟨g1, g2⟩ := Formalism.CountingSumsFrames.Top.lemma4Geom (p : ℝ) (a : ℝ) (Bo p F deg j x) (F.dist j (F.oldest j x))
      (((F.letters j).filter (fun y => Even y ∧ y < x ∧ ∀ l < r, y ≠ Arow F x l)).image
          (fun y => ((F.oldest j x - y) / 2).toNat)) (fun m => (dd (F.oldest j x - 2 * (m : ℤ)) : ℝ))
      (by exact_mod_cast hp) (by exact_mod_cast Nat.pos_of_ne_zero ha) hB (by
        intro m hm
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hm
        obtain ⟨h1, h2⟩ := hf y hy
        refine ⟨h2, Nat.cast_nonneg _, ?_⟩
        have h3 : F.oldest j x - 2 * ((((F.oldest j x - y) / 2).toNat : ℕ) : ℤ) = y := by omega
        have h4 : F.dist j y = F.dist j (F.oldest j x) + 2 * ((F.oldest j x - y) / 2).toNat := by
          have := (hY y hy).1
          unfold Frames.dist
          omega
        show (dd (F.oldest j x - 2 * ((((F.oldest j x - y) / 2).toNat : ℕ) : ℤ)) : ℝ) ≤ _
        rw [h3, ← h4, mul_div_assoc]
        exact hdd' y hy)
    exact le_trans g1 g2

end Formalism.MainNotions.G.symbolGeneratorData
