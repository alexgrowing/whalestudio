import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.LevImgCoeffBigM

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.Proposition5Numerics

open Formalism.MainNotions.G Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideWords

section Bij

variable {n' r : ℕ} [NeZero n'] (Fr : Frames n' r) {L₁ N₁ : ℕ}

theorem dg_posOf_val (x : ℤ) : ((posOf n' x).val : ℤ) = x % n' := by
  have hn : (0 : ℤ) < n' := by exact_mod_cast NeZero.pos n'
  have h0 : 0 ≤ x % n' := Int.emod_nonneg _ hn.ne'
  have h1 : x % n' < n' := Int.emod_lt_of_pos _ hn
  simp only [posOf]
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

theorem dg_posOf_inj {y a b : ℤ} (ha : y ≤ a ∧ a < y + n') (hb : y ≤ b ∧ b < y + n') (h : posOf n' a = posOf n' b) :
    a = b := by
  have hn : (0 : ℤ) < n' := by exact_mod_cast NeZero.pos n'
  have hv := congrArg (fun t : Fin n' => (t.val : ℤ)) h
  simp only [dg_posOf_val] at hv
  have e1 := Int.mul_ediv_add_emod a n'
  have e2 := Int.mul_ediv_add_emod b n'
  have hk : a - b = n' * (a / n' - b / n') := by
    rw [hv] at e1
    linear_combination e2 - e1
  have hlt : a - b < n' := by linarith [ha.2, hb.1]
  have hgt : -(n' : ℤ) < a - b := by linarith [ha.1, hb.2]
  rw [hk] at hlt hgt
  have h1 : a / n' - b / n' < 1 := by
    by_contra hc
    push_neg at hc
    nlinarith
  have h2 : -1 < a / n' - b / n' := by
    by_contra hc
    push_neg at hc
    nlinarith
  have h3 : a / n' - b / n' = 0 := by omega
  rw [h3, mul_zero] at hk
  linarith

variable {Fr}

theorem dg_fr_lt (hV : Fr.Valid L₁ N₁) (j : ℤ) (i : ℕ) : ∀ i', i < i' → i' < r → Fr.fr j i < Fr.fr j i' := by
  intro i' hii' hi'
  induction i' with
  | zero => omega
  | succ k ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp hii' with h | h
    · exact lt_trans (ih h (by omega)) (hV.2.2.1 j k (by omega))
    · subst h
      exact hV.2.2.1 j i (by omega)

theorem dg_fr_le (hV : Fr.Valid L₁ N₁) (j : ℤ) {i i' : ℕ} (h : i ≤ i') (h' : i' < r) : Fr.fr j i ≤ Fr.fr j i' := by
  rcases h.lt_or_eq with h | h
  · exact (dg_fr_lt hV j i i' h h').le
  · subst h
    exact le_rfl

theorem dg_z_mono (hV : Fr.Valid L₁ N₁) (hr : 1 ≤ r) : StrictMono fun j : ℤ => Fr.fr j (r - 1) := by
  apply strictMono_int_of_lt_succ
  intro j
  exact lt_of_lt_of_le (hV.2.2.2.1 j) (dg_fr_le hV (j + 1) (Nat.zero_le _) (by omega))

theorem frame_end_lt_next_start (hV : Fr.Valid L₁ N₁) (j : ℤ) : Fr.fr (j - 1) (r - 1) < Fr.fr j 0 := by
  have h := hV.2.2.2.1 (j - 1)
  rwa [sub_add_cancel] at h

theorem dg_llPos_eq (j : ℤ) (l : ℕ) (hl : l < (Fr.LLset j).card) :
    llPos Fr j l = (Fr.LLset j).orderEmbOfFin rfl ⟨l, hl⟩ := by
  simp [llPos, Finset.orderEmbOfFin_apply, hl]

theorem dg_llPos_mem (j : ℤ) (l : ℕ) (hl : l < (Fr.LLset j).card) : llPos Fr j l ∈ Fr.LLset j := by
  rw [dg_llPos_eq j l hl]
  exact Finset.orderEmbOfFin_mem _ _ _

theorem dg_mem_LL {j t : ℤ} : t ∈ Fr.LLset j ↔ (Fr.fr (j - 1) (r - 1) < t ∧ t < Fr.fr j 0) ∧ posOf n' t ∈ Fr.TT := by
  simp [Frames.LLset, Finset.mem_filter, Finset.mem_Ioo]

variable {J : ℕ} [NeZero J] {nL : ZMod J → ℕ}

theorem dg_posTL_mem (hV : Fr.Valid L₁ N₁) (hr : 1 ≤ r) (hnL : ∀ j, nL j = (Fr.LLset (segZ j)).card) (x : TL J nL r) :
    Fr.fr (segZ x.1 - 1) (r - 1) < posTL Fr x ∧ posTL Fr x ≤ Fr.fr (segZ x.1) (r - 1) := by
  obtain ⟨j, l | m⟩ := x
  · have hl : l.val < (Fr.LLset (segZ j)).card := by rw [← hnL j]; exact l.2
    have hmem := dg_mem_LL.mp (dg_llPos_mem (segZ j) l.val hl)
    refine ⟨hmem.1.1, ?_⟩
    exact le_trans hmem.1.2.le (dg_fr_le hV _ (Nat.zero_le _) (by omega))
  · refine ⟨?_, ?_⟩
    · exact lt_of_lt_of_le (frame_end_lt_next_start hV (segZ j)) (dg_fr_le hV _ (Nat.zero_le _) (by omega))
    · exact dg_fr_le hV _ (by omega) (by omega)

theorem dg_segZ_range (j : ZMod J) : 0 ≤ segZ j ∧ segZ j < J := by
  simp only [segZ]
  exact ⟨by positivity, by exact_mod_cast ZMod.val_lt j⟩

theorem dg_segZ_inj {j j' : ZMod J} (h : segZ j = segZ j') : j = j' := by
  have h' : (j.val : ℤ) = j'.val := h
  exact ZMod.val_injective J (by exact_mod_cast h')

theorem dg_posTL_inj (hV : Fr.Valid L₁ N₁) (hr : 1 ≤ r) (hnL : ∀ j, nL j = (Fr.LLset (segZ j)).card) :
    Function.Injective (posTL Fr : TL J nL r → ℤ) := by
  intro x y hxy
  have hx := dg_posTL_mem hV hr hnL x
  have hy := dg_posTL_mem hV hr hnL y
  have hmono := (dg_z_mono hV hr).monotone
  have hseg : segZ x.1 = segZ y.1 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have h1 : Fr.fr (segZ x.1) (r - 1) ≤ Fr.fr (segZ y.1 - 1) (r - 1) := hmono (by omega)
      rw [hxy] at hx
      omega
    · have h1 : Fr.fr (segZ y.1) (r - 1) ≤ Fr.fr (segZ x.1 - 1) (r - 1) := hmono (by omega)
      rw [hxy] at hx
      omega
  have hj : x.1 = y.1 := dg_segZ_inj hseg
  obtain ⟨j, a⟩ := x
  obtain ⟨j', b⟩ := y
  simp only at hj
  subst hj
  have hab : a = b := by
    rcases a with l | m <;> rcases b with l' | m'
    · have hl : l.val < (Fr.LLset (segZ j)).card := by rw [← hnL j]; exact l.2
      have hl' : l'.val < (Fr.LLset (segZ j)).card := by rw [← hnL j]; exact l'.2
      have e : llPos Fr (segZ j) l.val = llPos Fr (segZ j) l'.val := hxy
      rw [dg_llPos_eq _ _ hl, dg_llPos_eq _ _ hl'] at e
      have e2 := (Finset.orderEmbOfFin (Fr.LLset (segZ j)) rfl).injective e
      have e3 : l.val = l'.val := Fin.mk.inj e2
      rw [Fin.ext e3]
    · exfalso
      have hl : l.val < (Fr.LLset (segZ j)).card := by rw [← hnL j]; exact l.2
      have hmem := dg_mem_LL.mp (dg_llPos_mem (segZ j) l.val hl)
      have e : llPos Fr (segZ j) l.val = Fr.fr (segZ j) (r - 1 - m'.val) := hxy
      have h0 : Fr.fr (segZ j) 0 ≤ Fr.fr (segZ j) (r - 1 - m'.val) :=
        dg_fr_le hV _ (Nat.zero_le _) (by omega)
      have h5 := hmem.1.2
      omega
    · exfalso
      have hl : l'.val < (Fr.LLset (segZ j)).card := by rw [← hnL j]; exact l'.2
      have hmem := dg_mem_LL.mp (dg_llPos_mem (segZ j) l'.val hl)
      have e : Fr.fr (segZ j) (r - 1 - m.val) = llPos Fr (segZ j) l'.val := hxy
      have h0 : Fr.fr (segZ j) 0 ≤ Fr.fr (segZ j) (r - 1 - m.val) :=
        dg_fr_le hV _ (Nat.zero_le _) (by omega)
      have h5 := hmem.1.2
      omega
    · have e : Fr.fr (segZ j) (r - 1 - m.val) = Fr.fr (segZ j) (r - 1 - m'.val) := hxy
      have hm : r - 1 - m.val = r - 1 - m'.val := by
        by_contra hne
        rcases lt_or_gt_of_ne hne with h | h
        · have := dg_fr_lt hV (segZ j) _ _ h (by omega)
          omega
        · have := dg_fr_lt hV (segZ j) _ _ h (by omega)
          omega
      have e3 : m.val = m'.val := by omega
      rw [Fin.ext e3]
  rw [hab]

theorem dg_window (hV : Fr.Valid L₁ N₁) (hr : 1 ≤ r) (hJ : J = Fr.J) (hnL : ∀ j, nL j = (Fr.LLset (segZ j)).card)
    (x : TL J nL r) :
    Fr.fr (-1) (r - 1) + 1 ≤ posTL Fr x ∧ posTL Fr x < Fr.fr (-1) (r - 1) + 1 + n' := by
  have hm := dg_posTL_mem hV hr hnL x
  have hs := dg_segZ_range x.1
  have hmono := (dg_z_mono hV hr).monotone
  have hJ' : (J : ℤ) = (Fr.J : ℤ) := by rw [hJ]
  have h1 : Fr.fr (-1) (r - 1) ≤ Fr.fr (segZ x.1 - 1) (r - 1) := hmono (by omega)
  have h2 : Fr.fr (segZ x.1) (r - 1) ≤ Fr.fr (-1 + (Fr.J : ℤ)) (r - 1) := hmono (by omega)
  have h3 := hV.2.1 (-1) (r - 1)
  constructor <;> omega

theorem dg_inj (hV : Fr.Valid L₁ N₁) (hr : 1 ≤ r) (hJ : J = Fr.J) (hnL : ∀ j, nL j = (Fr.LLset (segZ j)).card) :
    Function.Injective fun x : TL J nL r => posOf n' (posTL Fr x) := by
  intro x y hxy
  have hx := dg_window hV hr hJ hnL x
  have hy := dg_window hV hr hJ hnL y
  exact dg_posTL_inj hV hr hnL (dg_posOf_inj hx hy hxy)

theorem dg_frame (hV : Fr.Valid L₁ N₁) (j t : ℤ) (ht : posOf n' t ∈ Fr.TT) (h0 : Fr.fr j 0 ≤ t) :
    ∀ i, i < r → t ≤ Fr.fr j i → ∃ i' ≤ i, t = Fr.fr j i' := by
  intro i
  induction i with
  | zero =>
    intro _ ht0
    exact ⟨0, le_rfl, le_antisymm ht0 h0⟩
  | succ k ih =>
    intro hk htk
    by_cases hle : t ≤ Fr.fr j k
    · obtain ⟨i', hi', he⟩ := ih (by omega) hle
      exact ⟨i', by omega, he⟩
    · push_neg at hle
      rcases htk.lt_or_eq with hlt | heq
      · exact absurd ht (hV.2.2.2.2.2.1 j k t (by omega) hle hlt)
      · exact ⟨k + 1, le_rfl, heq⟩

theorem dg_surj (hV : Fr.Valid L₁ N₁) (hr : 1 ≤ r) (hJ : J = Fr.J) (hnL : ∀ j, nL j = (Fr.LLset (segZ j)).card) :
    ∀ s ∈ Fr.TT, ∃ x : TL J nL r, posOf n' (posTL Fr x) = s := by
  intro s hs
  have hn : (0 : ℤ) < n' := by exact_mod_cast NeZero.pos n'
  obtain ⟨t, ht1, ht2, hpos⟩ : ∃ t : ℤ, Fr.fr (-1) (r - 1) < t ∧ t ≤ Fr.fr (-1) (r - 1) + n' ∧
      posOf n' t = s := by
    refine ⟨Fr.fr (-1) (r - 1) + 1 + ((s.val : ℤ) - (Fr.fr (-1) (r - 1) + 1)) % n', ?_, ?_, ?_⟩
    · have := Int.emod_nonneg ((s.val : ℤ) - (Fr.fr (-1) (r - 1) + 1)) hn.ne'
      omega
    · have := Int.emod_lt_of_pos ((s.val : ℤ) - (Fr.fr (-1) (r - 1) + 1)) hn
      omega
    · apply Fin.ext
      have h1 := dg_posOf_val (n' := n')
        (Fr.fr (-1) (r - 1) + 1 + ((s.val : ℤ) - (Fr.fr (-1) (r - 1) + 1)) % n')
      have h2 : (Fr.fr (-1) (r - 1) + 1 + ((s.val : ℤ) - (Fr.fr (-1) (r - 1) + 1)) % n') % n' =
          s.val := by
        rw [Int.emod_def ((s.val : ℤ) - (Fr.fr (-1) (r - 1) + 1)) n']
        have e : Fr.fr (-1) (r - 1) + 1 + ((s.val : ℤ) - (Fr.fr (-1) (r - 1) + 1) -
            n' * (((s.val : ℤ) - (Fr.fr (-1) (r - 1) + 1)) / n')) =
            (s.val : ℤ) + n' * (-(((s.val : ℤ) - (Fr.fr (-1) (r - 1) + 1)) / n')) := by ring
        rw [e, Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by positivity) (by exact_mod_cast s.2)]
      rw [h2] at h1
      exact_mod_cast h1
  have hJ1 : 1 ≤ J := Nat.one_le_iff_ne_zero.mpr (NeZero.ne J)
  have hper := hV.2.1 (-1) (r - 1)
  have hJc : ((J - 1 : ℕ) : ℤ) = -1 + (Fr.J : ℤ) := by
    rw [← hJ]
    push_cast [Nat.cast_sub hJ1]
    ring
  have hwit : t ≤ Fr.fr ((J - 1 : ℕ) : ℤ) (r - 1) := by
    rw [hJc, hper]
    exact ht2
  have hex : ∃ k : ℕ, t ≤ Fr.fr (k : ℤ) (r - 1) := ⟨J - 1, hwit⟩
  have hkspec : t ≤ Fr.fr ((Nat.find hex : ℕ) : ℤ) (r - 1) := Nat.find_spec hex
  have hkJ : Nat.find hex ≤ J - 1 := Nat.find_min' hex hwit
  have hklow : Fr.fr (((Nat.find hex : ℕ) : ℤ) - 1) (r - 1) < t := by
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | h0
    · rw [h0, Nat.cast_zero, zero_sub]
      exact ht1
    · have hm := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
      push_neg at hm
      have e : (((Nat.find hex - 1 : ℕ)) : ℤ) = ((Nat.find hex : ℕ) : ℤ) - 1 := by omega
      rw [e] at hm
      exact hm
  have hseg : segZ ((Nat.find hex : ℕ) : ZMod J) = ((Nat.find hex : ℕ) : ℤ) := by
    simp only [segZ, ZMod.val_natCast]
    rw [Nat.mod_eq_of_lt (by omega)]
  have hsT : posOf n' t ∈ Fr.TT := by rw [hpos]; exact hs
  by_cases htl : t < Fr.fr ((Nat.find hex : ℕ) : ℤ) 0
  · have hmemLL : t ∈ Fr.LLset ((Nat.find hex : ℕ) : ℤ) := dg_mem_LL.mpr ⟨⟨hklow, htl⟩, hsT⟩
    obtain ⟨i, hi⟩ : ∃ i, (Fr.LLset ((Nat.find hex : ℕ) : ℤ)).orderEmbOfFin rfl i = t := by
      have hr' : t ∈ Set.range ((Fr.LLset ((Nat.find hex : ℕ) : ℤ)).orderEmbOfFin rfl) := by
        rw [Finset.range_orderEmbOfFin]
        exact hmemLL
      exact hr'
    have hiL : i.val < nL ((Nat.find hex : ℕ) : ZMod J) := by
      rw [hnL, hseg]
      exact i.2
    refine ⟨⟨((Nat.find hex : ℕ) : ZMod J), Sum.inl ⟨i.val, hiL⟩⟩, ?_⟩
    show posOf n' (llPos Fr (segZ ((Nat.find hex : ℕ) : ZMod J)) i.val) = s
    rw [hseg, dg_llPos_eq _ _ i.2, Fin.eta, hi, hpos]
  · push_neg at htl
    obtain ⟨i', hi', he⟩ := dg_frame hV ((Nat.find hex : ℕ) : ℤ) t hsT htl (r - 1) (by omega) hkspec
    refine ⟨⟨((Nat.find hex : ℕ) : ZMod J), Sum.inr ⟨r - 1 - i', by omega⟩⟩, ?_⟩
    show posOf n' (Fr.fr (segZ ((Nat.find hex : ℕ) : ZMod J)) (r - 1 - (r - 1 - i'))) = s
    rw [hseg, show r - 1 - (r - 1 - i') = i' by omega, ← he, hpos]

end Bij

theorem digFacts {n' r K m : ℕ} [NeZero n'] (Fr : Frames n' r) (p : ℕ) (hp : p.Prime) (O : Type) [CommRing O]
    [IsDomain O] [CharZero (KK O)] (hk : m + 1 = r + K) {J : ℕ} [NeZero J] (nL : ZMod J → ℕ) (L₁ N₁ : ℕ)
    (hV : Fr.Valid L₁ N₁) (hr : 1 ≤ r) (hJ : J = Fr.J) (hnL : ∀ j, nL j = (Fr.LLset (segZ j)).card)
    (d : Fin n' → ℕ) (hd : ∀ s, s ∉ Fr.TT → d s = 0) : DigFacts Fr p O hk nL d :=
  digFacts_of Fr p O hk nL hp.pos (dg_inj hV hr hJ hnL) (dg_surj hV hr hJ hnL) d hd

end Formalism.MainNotions.Proposition5Numerics
