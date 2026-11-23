import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.SPbound

noncomputable section

open Finset Classical

namespace Formalism.MainNotions.Pf14

open Formalism.MainNotions.G Formalism.MainNotions.SourceCleaning Formalism.MainNotions.G.WittFrameLocaliserOrders

section Bound

variable (p n' : ℕ) [Fact p.Prime] [NeZero n'] {r : ℕ} (F : Frames n' r)

theorem eDel_apply (j : ℤ) (t : Fin n') : eDel p n' F j t =
    ∑ l : Fin r, if t = posOf n' (F.fr j l.val) then p ^ (zF F j - F.fr j l.val).toNat else 0 := by
  simp only [eDel, Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one,
    mul_zero]

theorem eD_apply (s : ℤ) (t : Fin n') : eD p n' F s t =
    ∑ l : Fin r, if t = posOf n' (Arow F s l.val) then p ^ (s - Arow F s l.val).toNat else 0 := by
  simp only [eD, Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one,
    mul_zero]

variable {p n' F} {TT : Finset (Fin n')} {L₁ L₂ N₁ G' : ℕ}

theorem del_bound (hF : FramesOK TT L₁ L₂ N₁ G' F) (hr : 1 ≤ r) (hG : G' ≤ n') (k c' : ℕ) (t : Fin n') :
    ∑ j ∈ Finset.range F.J, (c' * alpha p F k (j : ℤ) + c') * eDel p n' F (j : ℤ) t ≤
      (c' * (1 + r * k * p ^ G') + c') * p ^ G' := by
  classical
  have hV := hF.2.1
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have rle : ∀ (j : ℤ) (i i' : ℕ), i ≤ i' → i' < r → F.fr j i ≤ F.fr j i' := by
    intro j i i' h h'
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    induction d with
    | zero => exact le_rfl
    | succ d ih =>
      exact le_trans (ih (by omega) (by omega)) (le_of_lt (hV.2.2.1 j (i + d) (by omega)))
  have rlt : ∀ (j : ℤ) (d : ℕ) (i i' : ℕ), i < r → i' < r → F.fr j i < F.fr (j + 1 + d) i' := by
    intro j d
    induction d with
    | zero =>
      intro i i' hi hi'
      have h1 := rle j i (r - 1) (by omega) (by omega)
      have h2 := hV.2.2.2.1 j
      have h3 := rle (j + 1) 0 i' (Nat.zero_le _) hi'
      simp only [Nat.cast_zero, add_zero]
      linarith
    | succ d ih =>
      intro i i' hi hi'
      have h1 := ih i (r - 1) hi (by omega)
      have h2 := hV.2.2.2.1 (j + 1 + d)
      have h3 := rle (j + 1 + d + 1) 0 i' (Nat.zero_le _) hi'
      have e : j + 1 + ((d + 1 : ℕ) : ℤ) = j + 1 + d + 1 := by push_cast; ring
      rw [e]
      linarith
  have hper := hV.2.1 0 0
  simp only [zero_add] at hper
  have hin : ∀ j : ℕ, j < F.J → ∀ l, l < r → F.fr 0 0 ≤ F.fr j l ∧ F.fr j l < F.fr 0 0 + n' := by
    intro j hj l hl
    constructor
    · rcases Nat.eq_zero_or_pos j with h | h
      · subst h
        simpa using rle 0 0 l (Nat.zero_le _) hl
      · have h1 := rlt 0 (j - 1) 0 l (by omega) hl
        have e : (0 : ℤ) + 1 + ((j - 1 : ℕ) : ℤ) = j := by omega
        rw [e] at h1
        linarith
    · have h1 := rlt j (F.J - j - 1) l 0 hl (by omega)
      have e : (j : ℤ) + 1 + ((F.J - j - 1 : ℕ) : ℤ) = F.J := by omega
      rw [e] at h1
      linarith
  have huniq : ∀ j j' : ℕ, j < F.J → j' < F.J → ∀ l l' : ℕ, l < r → l' < r →
      posOf n' (F.fr j l) = posOf n' (F.fr j' l') → j = j' ∧ l = l' := by
    intro j j' hj hj' l l' hl hl' h
    have he := residue_position_injective_window n' (F.fr 0 0) _ _ (hin j hj l hl) (hin j' hj' l' hl') h
    rcases lt_trichotomy j j' with h1 | h1 | h1
    · exfalso
      have h2 := rlt j (j' - j - 1) l l' hl hl'
      have e : (j : ℤ) + 1 + ((j' - j - 1 : ℕ) : ℤ) = j' := by omega
      rw [e] at h2
      linarith
    · subst h1
      refine ⟨rfl, ?_⟩
      by_contra hne
      rcases lt_or_gt_of_ne hne with h2 | h2
      · have h3 := hV.2.2.1 j l (by omega)
        have h4 := rle j (l + 1) l' (by omega) hl'
        linarith
      · have h3 := hV.2.2.1 j l' (by omega)
        have h4 := rle j (l' + 1) l (by omega) hl
        linarith
    · exfalso
      have h2 := rlt j' (j - j' - 1) l' l hl' hl
      have e : (j' : ℤ) + 1 + ((j - j' - 1 : ℕ) : ℤ) = j := by omega
      rw [e] at h2
      linarith
  by_cases hex : ∃ j0 ∈ Finset.range F.J, ∃ l0 : Fin r, t = posOf n' (F.fr (j0 : ℤ) l0.val)
  · obtain ⟨j0, hj0, l0, ht0⟩ := hex
    have hj0' := Finset.mem_range.1 hj0
    have hz : ∀ j ∈ Finset.range F.J, j ≠ j0 →
        (c' * alpha p F k (j : ℤ) + c') * eDel p n' F (j : ℤ) t = 0 := by
      intro j hj hne
      rw [eDel_apply, Finset.sum_eq_zero, mul_zero]
      intro l _
      refine if_neg ?_
      intro h
      exact hne (huniq j j0 (Finset.mem_range.1 hj) hj0' l l0 l.isLt l0.isLt (h.symm.trans ht0)).1
    have h0 : eDel p n' F (j0 : ℤ) t = p ^ (zF F (j0 : ℤ) - F.fr j0 l0.val).toNat := by
      rw [eDel_apply, Finset.sum_eq_single l0]
      · exact if_pos ht0
      · intro l _ hne
        refine if_neg ?_
        intro h
        exact hne (Fin.ext (huniq j0 j0 hj0' hj0' l l0 l.isLt l0.isLt (h.symm.trans ht0)).2)
      · intro h
        exact absurd (Finset.mem_univ l0) h
    rw [Finset.sum_eq_single j0 hz (fun h => absurd hj0 h), h0]
    apply Nat.mul_le_mul
    · have hzz : (zF F ((j0 : ℤ) + 1) - zF F (j0 : ℤ)).toNat ≤ G' := by
        have g := hF.2.2.1 ((j0 : ℤ) + 1)
        simp only [add_sub_cancel_right] at g
        have m0 := rle (j0 : ℤ) 0 (r - 1) (Nat.zero_le _) (by omega)
        simp only [zF]
        omega
      have hα : alpha p F k (j0 : ℤ) ≤ 1 + r * k * p ^ G' := by
        simp only [alpha, Qj]
        have h1 : (if (j0 : ℤ) = 0 then 1 else 0) ≤ 1 := by split_ifs <;> omega
        exact add_le_add h1 (Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
          (le_trans (Nat.sub_le _ _) (Nat.pow_le_pow_right hp hzz)))
      exact Nat.add_le_add_right (Nat.mul_le_mul_left c' hα) c'
    · apply Nat.pow_le_pow_right hp
      have g := hF.2.2.1 (j0 : ℤ)
      have m := rlt ((j0 : ℤ) - 1) 0 0 l0.val (by omega) l0.isLt
      simp only [Nat.cast_zero, add_zero, sub_add_cancel] at m
      simp only [zF]
      omega
  · push_neg at hex
    refine le_trans (le_of_eq (Finset.sum_eq_zero fun j hj => ?_)) (Nat.zero_le _)
    rw [eDel_apply, Finset.sum_eq_zero (fun l _ => if_neg (hex j hj l)), mul_zero]

private theorem nuRow_le_Sc_add_wSz {L₁ N₁ : ℕ} (hV : F.Valid L₁ N₁) (j : ℤ) {i i' : ℕ} (h : i ≤ i') (h' : i' < r) :
    F.fr j i ≤ F.fr j i' := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  induction d with
  | zero => exact le_rfl
  | succ d ih =>
    have h1 := ih (by omega) (by omega)
    have h2 := hV.2.2.1 j (i + d) (by omega)
    exact le_trans h1 (le_of_lt h2)

private theorem fr_lt_fr_of_lt_index {L₁ N₁ : ℕ} (hV : F.Valid L₁ N₁) {j j' : ℤ} (hjj : j < j') {i i' : ℕ}
    (hi : i < r) (hi' : i' < r) : F.fr j i < F.fr j' i' := by
  have key : ∀ d : ℕ, ∀ i', i' < r → F.fr j i < F.fr (j + 1 + d) i' := by
    intro d
    induction d with
    | zero =>
      intro i' hi'
      have h1 := nuRow_le_Sc_add_wSz hV j (show i ≤ r - 1 by omega) (by omega)
      have h2 := hV.2.2.2.1 j
      have h3 := nuRow_le_Sc_add_wSz hV (j + 1) (Nat.zero_le i') hi'
      simp only [Nat.cast_zero, add_zero]
      linarith
    | succ d ih =>
      intro i' hi'
      have h1 := ih (r - 1) (by omega)
      have h2 := hV.2.2.2.1 (j + 1 + d)
      have h3 := nuRow_le_Sc_add_wSz hV (j + 1 + d + 1) (Nat.zero_le i') hi'
      have e : j + 1 + ((d + 1 : ℕ) : ℤ) = j + 1 + d + 1 := by push_cast; ring
      rw [e]
      linarith
  obtain ⟨d, hd⟩ : ∃ d : ℕ, j' = j + 1 + d := ⟨(j' - j - 1).toNat, by omega⟩
  subst hd
  exact key d i' hi'

private theorem arow_lt_self_and_sub_lt_of_framesOK (hF : FramesOK TT L₁ L₂ N₁ G' F) (hr : 1 ≤ r) (hG : G' ≤ n')
    (s : ℤ) (l : ℕ) (hl : l < r) : Arow F s l < s ∧ s - Arow F s l < G' := by
  classical
  have hV := hF.2.1
  have hstep : ∀ j : ℤ, F.fr j (r - 1) + 1 ≤ F.fr (j + 1) (r - 1) := fun j => by
    have := fr_lt_fr_of_lt_index hV (lt_add_one j) (i := r - 1) (i' := r - 1) (by omega) (by omega)
    omega
  have hup : ∀ m : ℕ, F.fr 0 (r - 1) + m ≤ F.fr m (r - 1) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have := hstep m
      push_cast
      linarith
  have hdown : ∀ m : ℕ, F.fr (-(m : ℤ)) (r - 1) + m ≤ F.fr 0 (r - 1) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have := hstep (-((m + 1 : ℕ) : ℤ))
      have e : -((m + 1 : ℕ) : ℤ) + 1 = -(m : ℤ) := by push_cast; ring
      rw [e] at this
      push_cast at this ⊢
      linarith
  obtain ⟨j0, hj0, hmax⟩ := Int.exists_greatest_of_bdd (P := fun z => F.fr z (r - 1) < s)
    ⟨(s - F.fr 0 (r - 1)).toNat, fun z hz => by
      rcases le_or_gt 0 z with h0 | h0
      · have := hup z.toNat
        rw [Int.toNat_of_nonneg h0] at this
        omega
      · omega⟩
    ⟨-((F.fr 0 (r - 1) - s + 1).toNat : ℤ), by
      have := hdown (F.fr 0 (r - 1) - s + 1).toNat
      show F.fr _ (r - 1) < s
      omega⟩
  have hj1 : s ≤ F.fr (j0 + 1) (r - 1) := by
    by_contra h
    have := hmax (j0 + 1) (show F.fr (j0 + 1) (r - 1) < s by omega)
    omega
  have hgap := hF.2.2.1 (j0 + 1)
  simp only [add_sub_cancel_right] at hgap
  have hnr : (n' : ℤ) ≤ (r : ℤ) * n' := by
    have : n' ≤ r * n' := Nat.le_mul_of_pos_left n' hr
    exact_mod_cast this
  have hmemA : ∀ i < r, F.fr j0 i ∈ evensBefore F s := by
    intro i hi
    have h0 := nuRow_le_Sc_add_wSz hV j0 (Nat.zero_le i) hi
    have h1 := nuRow_le_Sc_add_wSz hV j0 (show i ≤ r - 1 by omega) (by omega)
    have h2 := hV.2.2.2.2.1 j0 i hi
    rw [Formalism.MainNotions.G.symbolGeneratorData.dv_ev_mem]
    refine ⟨⟨?_, ?_⟩, h2.1, h2.2⟩
    · have : (G' : ℤ) ≤ n' := by exact_mod_cast hG
      linarith
    · linarith
  have hinj : Set.InjOn (fun i => F.fr j0 i) (Finset.range r : Set ℕ) := by
    intro a ha b hb hab
    simp only [Finset.coe_range, Set.mem_Iio] at ha hb hab
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have h1 := hV.2.2.1 j0 a (by omega)
      have h2 := nuRow_le_Sc_add_wSz hV j0 (show a + 1 ≤ b by omega) hb
      linarith
    · have h1 := hV.2.2.1 j0 b (by omega)
      have h2 := nuRow_le_Sc_add_wSz hV j0 (show b + 1 ≤ a by omega) ha
      linarith
  have hcardA : ((Finset.range r).image fun i => F.fr j0 i).card = r := by
    rw [Finset.card_image_of_injOn hinj, Finset.card_range]
  have hpw : (evensBefore F s).Pairwise (· > ·) := evensBefore_pairwise F s
  have hlen : r ≤ (evensBefore F s).length := by
    calc r = ((Finset.range r).image fun i => F.fr j0 i).card := hcardA.symm
      _ ≤ (evensBefore F s).toFinset.card := by
        apply Finset.card_le_card
        intro a ha
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 ha
        exact List.mem_toFinset.2 (hmemA i (Finset.mem_range.1 hi))
      _ ≤ (evensBefore F s).length := List.toFinset_card_le _
  have hl' : l < (evensBefore F s).length := by omega
  have harow : Arow F s l = (evensBefore F s)[l] := by
    simp only [Arow]
    exact List.getD_eq_getElem _ _ hl'
  have hyl : (evensBefore F s)[l] < s := by
    have := (Formalism.MainNotions.G.symbolGeneratorData.dv_ev_mem (F := F) s _).1 (List.getElem_mem hl')
    exact this.1.2
  have hge : F.fr j0 0 ≤ (evensBefore F s)[l] := by
    by_contra hlt
    push_neg at hlt
    have hsub : ((Finset.range r).image fun i => F.fr j0 i) ⊆ ((evensBefore F s).take l).toFinset := by
      intro a ha
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 ha
      have hi' := Finset.mem_range.1 hi
      have hm : F.fr j0 i ∈ (evensBefore F s).take l ++ (evensBefore F s).drop l := by
        rw [List.take_append_drop]
        exact hmemA i hi'
      rcases List.mem_append.1 hm with h | h
      · exact List.mem_toFinset.2 h
      · exfalso
        have hpw' := hpw.sublist (List.drop_sublist l (evensBefore F s))
        rw [List.drop_eq_getElem_cons hl'] at h hpw'
        have h0 := nuRow_le_Sc_add_wSz hV j0 (Nat.zero_le i) hi'
        rcases List.mem_cons.1 h with h | h
        · linarith
        · have := List.rel_of_pairwise_cons hpw' h
          linarith
    have := Finset.card_le_card hsub
    have h2 := List.toFinset_card_le ((evensBefore F s).take l)
    have h3 := List.length_take_le l (evensBefore F s)
    omega
  rw [harow]
  constructor
  · exact hyl
  · linarith

theorem tops_near (hF : FramesOK TT L₁ L₂ N₁ G' F) (hr : 1 ≤ r) (hG : G' ≤ n')
    (hI : Formalism.G0.CondIntervals n' (F.TT.map Fin.valEmbedding) G' N₁) (t : Fin n') :
    (F.TT.filter fun s => ∃ l : Fin r, t = posOf n' (Arow F (s.val : ℤ) l.val)).card ≤ N₁ + 1 := by
  classical
  refine le_trans ?_ (Nat.le_succ N₁)
  have hsub : ((F.TT.filter fun s => ∃ l : Fin r, t = posOf n' (Arow F (s.val : ℤ) l.val)).map
      Fin.valEmbedding) ⊆ (F.TT.map Fin.valEmbedding) ∩ Formalism.G0.window n' t.val G' := by
    intro x hx
    simp only [Finset.mem_map, Finset.mem_filter, Fin.valEmbedding_apply] at hx
    obtain ⟨s, ⟨hs, l, hl⟩, rfl⟩ := hx
    refine Finset.mem_inter.2 ⟨Finset.mem_map_of_mem _ hs, ?_⟩
    obtain ⟨h1, h2⟩ := arow_lt_self_and_sub_lt_of_framesOK hF hr hG (s.val : ℤ) l.val l.isLt
    have hn0 : (0 : ℤ) < n' := by exact_mod_cast NeZero.pos n'
    have ht : (t.val : ℤ) = Arow F (s.val : ℤ) l.val % n' := by
      rw [hl]
      simp only [posOf]
      have e0 : 0 ≤ Arow F (s.val : ℤ) l.val % (n' : ℤ) := Int.emod_nonneg _ (ne_of_gt hn0)
      have e1 : Arow F (s.val : ℤ) l.val % (n' : ℤ) < n' := Int.emod_lt_of_pos _ hn0
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    have hs' : (s.val : ℤ) < n' := by exact_mod_cast s.isLt
    simp only [Formalism.G0.window, Finset.mem_image, Finset.mem_range]
    refine ⟨((s.val : ℤ) - Arow F (s.val : ℤ) l.val).toNat, by omega, ?_⟩
    have key : (((t.val + ((s.val : ℤ) - Arow F (s.val : ℤ) l.val).toNat : ℕ) : ℤ) % n') = s.val := by
      push_cast
      rw [Int.toNat_of_nonneg (by omega), ht, Int.emod_add_emod]
      rw [show Arow F (s.val : ℤ) l.val + ((s.val : ℤ) - Arow F (s.val : ℤ) l.val) = s.val by ring]
      exact Int.emod_eq_of_lt (by positivity) hs'
    exact_mod_cast key
  calc _ = _ := (Finset.card_map _).symm
    _ ≤ _ := Finset.card_le_card hsub
    _ ≤ N₁ := hI t.val t.isLt

theorem d_bound (hF : FramesOK TT L₁ L₂ N₁ G' F) (hr : 1 ≤ r) (hG : G' ≤ n')
    (hI : Formalism.G0.CondIntervals n' (F.TT.map Fin.valEmbedding) G' N₁) (mu : ℕ) (t : Fin n') :
    ∑ s ∈ F.TT, mu * eD p n' F (s.val : ℤ) t ≤ (N₁ + 1) * (mu * (r * p ^ G')) := by
  classical
  have hp : 0 < p := (Fact.out : p.Prime).pos
  rw [← Finset.sum_filter_of_ne (p := fun s : Fin n' => ∃ l : Fin r, t = posOf n' (Arow F (s.val : ℤ) l.val))]
  · refine le_trans (Finset.sum_le_card_nsmul _ _ (mu * (r * p ^ G')) ?_) ?_
    · intro s _
      apply Nat.mul_le_mul_left
      rw [eD_apply]
      calc ∑ l : Fin r, (if t = posOf n' (Arow F (s.val : ℤ) l.val)
              then p ^ ((s.val : ℤ) - Arow F (s.val : ℤ) l.val).toNat else 0)
          ≤ ∑ _l : Fin r, p ^ G' := Finset.sum_le_sum fun l _ => by
            split_ifs
            · apply Nat.pow_le_pow_right hp
              have := (arow_lt_self_and_sub_lt_of_framesOK hF hr hG (s.val : ℤ) l.val l.isLt).2
              omega
            · exact Nat.zero_le _
        _ = r * p ^ G' := by simp
    · rw [smul_eq_mul]
      exact Nat.mul_le_mul_right _ (tops_near hF hr hG hI t)
  · intro s _ hne
    by_contra hno
    push_neg at hno
    apply hne
    rw [eD_apply, Finset.sum_eq_zero, mul_zero]
    intro l _
    exact if_neg (hno l)

theorem eSP_off (hF : FramesOK TT L₁ L₂ N₁ G' F) (k c' Q : ℕ) (t : Fin n') (ht : t ∉ F.TT) :
    eSP p n' F k c' Q t = 0 := by
  have hV := hF.2.1
  have h1 : ∀ j : ℤ, eDel p n' F j t = 0 := by
    intro j
    rw [eDel_apply]
    refine Finset.sum_eq_zero fun l _ => if_neg ?_
    rintro rfl
    exact ht (hV.2.2.2.2.1 j l.val l.isLt).1
  have h2 : ∀ s ∈ F.TT, eD p n' F (s.val : ℤ) t = 0 := by
    intro s hs
    rw [eD_apply]
    refine Finset.sum_eq_zero fun l _ => if_neg ?_
    rintro rfl
    exact ht (bs_top_Arow F s hs l.val)
  simp only [eSP, Pi.add_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul, h1, mul_zero,
    Finset.sum_const_zero, add_zero, zero_add]
  exact Finset.sum_eq_zero fun s hs => by rw [h2 s hs, mul_zero]

theorem eSP_le (hF : FramesOK TT L₁ L₂ N₁ G' F) (hr : 1 ≤ r) (hG : G' ≤ n')
    (hI : Formalism.G0.CondIntervals n' (F.TT.map Fin.valEmbedding) G' N₁) (k c' : ℕ) (t : Fin n') :
    eSP p n' F k c' (p ^ G') t ≤ (c' * (1 + r * k * p ^ G') + c') * p ^ G' +
      (N₁ + 1) * (((2 * p ^ G' + 3) * c' + k * p ^ G') * (r * p ^ G')) := by
  have h1 := del_bound (p := p) hF hr hG k c' t
  have h2 := d_bound (p := p) hF hr hG hI ((2 * p ^ G' + 3) * c' + k * p ^ G') t
  have e : c' * ∑ j ∈ Finset.range F.J, alpha p F k (j : ℤ) * eDel p n' F (j : ℤ) t +
      ∑ j ∈ Finset.range F.J, c' * eDel p n' F (j : ℤ) t =
      ∑ j ∈ Finset.range F.J, (c' * alpha p F k (j : ℤ) + c') * eDel p n' F (j : ℤ) t := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  simp only [eSP, Pi.add_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  rw [e]
  exact add_le_add h1 h2

end Bound

end Formalism.MainNotions.Pf14
