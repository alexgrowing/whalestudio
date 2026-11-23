import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.Transported

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G

variable {n' : ℕ}

theorem cd_cases (x y : Fin n') :
    (x.val ≤ y.val ∧ cdist x y = y.val - x.val) ∨ (y.val < x.val ∧ cdist x y = y.val + n' - x.val) := by
  have hx := x.isLt
  have hy := y.isLt
  unfold cdist
  rcases le_or_gt x.val y.val with h | h
  · left
    refine ⟨h, ?_⟩
    rw [show y.val + n' - x.val = (y.val - x.val) + n' by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]
  · right
    exact ⟨h, Nat.mod_eq_of_lt (by omega)⟩

theorem posAdd_cdist (x y : Fin n') : posAdd x (cdist x y) = y := by
  apply Fin.ext
  show (x.val + cdist x y) % n' = y.val
  rcases cd_cases x y with ⟨h, e⟩ | ⟨h, e⟩
  · rw [e, show x.val + (y.val - x.val) = y.val by omega, Nat.mod_eq_of_lt y.isLt]
  · rw [e, show x.val + (y.val + n' - x.val) = y.val + n' by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt y.isLt]

theorem ev_mono (TT : Finset (Fin n')) : StrictMono (evenTops TT).get := (Finset.sortedLT_sort _).strictMono_get

theorem ev_mem (TT : Finset (Fin n')) (x : Fin n') : x ∈ evenTops TT ↔ x ∈ TT ∧ Even x.val := by
  simp [evenTops, Finset.mem_sort, Finset.mem_filter]

theorem numSeg_eq (TT : Finset (Fin n')) : numSeg TT = (TT.filter (fun s => Even s.val)).card := by
  simp [numSeg, evenTops, Finset.length_sort]

theorem start_mem (TT : Finset (Fin n')) (j : Fin (numSeg TT)) :
    segStart TT j ∈ TT ∧ Even (segStart TT j).val := (ev_mem TT _).1 (List.get_mem _ _)

theorem next_mem (TT : Finset (Fin n')) (j : Fin (numSeg TT)) :
    segNext TT j ∈ TT ∧ Even (segNext TT j).val := (ev_mem TT _).1 (List.get_mem _ _)

private lemma cdist_next_pos_and_le_of_strictMono (L : List (Fin n')) (hL : StrictMono L.get) (j i' m : Fin L.length)
    (hi : i'.val = (j.val + 1) % L.length) (hmj : m.val ≠ j.val) :
    0 < cdist (L.get j) (L.get i') ∧ cdist (L.get j) (L.get i') ≤ cdist (L.get j) (L.get m) := by

  have lt_iff : ∀ a b : Fin L.length, (L.get a).val < (L.get b).val ↔ a.val < b.val := fun a b =>
    (Fin.lt_def.symm.trans hL.lt_iff_lt).trans Fin.lt_def
  have hj := j.isLt
  have hm := m.isLt
  have hs := (L.get j).isLt
  have hnx := (L.get i').isLt
  have he := (L.get m).isLt
  rcases Nat.lt_or_ge (j.val + 1) L.length with hk | hk
  · rw [Nat.mod_eq_of_lt hk] at hi
    have a1 : (L.get j).val < (L.get i').val := (lt_iff j i').2 (by omega)
    rcases Nat.lt_or_gt_of_ne hmj with hmj' | hmj'
    · have a2 : (L.get m).val < (L.get j).val := (lt_iff m j).2 hmj'
      rcases cd_cases (L.get j) (L.get i') with ⟨_, e1⟩ | ⟨_, e1⟩ <;>
      rcases cd_cases (L.get j) (L.get m) with ⟨_, e2⟩ | ⟨_, e2⟩ <;> omega
    · have a2 : ¬ (L.get m).val < (L.get i').val := fun h => by have := (lt_iff m i').1 h; omega
      rcases cd_cases (L.get j) (L.get i') with ⟨_, e1⟩ | ⟨_, e1⟩ <;>
      rcases cd_cases (L.get j) (L.get m) with ⟨_, e2⟩ | ⟨_, e2⟩ <;> omega
  · have hk' : j.val + 1 = L.length := by omega
    rw [hk', Nat.mod_self] at hi
    have hmj' : m.val < j.val := by omega
    have a1 : (L.get i').val < (L.get j).val := (lt_iff i' j).2 (by omega)
    have a2 : (L.get m).val < (L.get j).val := (lt_iff m j).2 hmj'
    have a3 : ¬ (L.get m).val < (L.get i').val := fun h => by have := (lt_iff m i').1 h; omega
    rcases cd_cases (L.get j) (L.get i') with ⟨_, e1⟩ | ⟨_, e1⟩ <;>
    rcases cd_cases (L.get j) (L.get m) with ⟨_, e2⟩ | ⟨_, e2⟩ <;> omega

theorem next_min (TT : Finset (Fin n')) (j : Fin (numSeg TT)) (e : Fin n') (he : e ∈ TT)
    (hev : Even e.val) (hne : e ≠ segStart TT j) :
    0 < cdist (segStart TT j) (segNext TT j) ∧
      cdist (segStart TT j) (segNext TT j) ≤ cdist (segStart TT j) e := by
  obtain ⟨m, hm⟩ := List.mem_iff_get.1 ((ev_mem TT e).2 ⟨he, hev⟩)
  subst hm
  have hmj : m.val ≠ j.val := fun h => hne (congrArg (evenTops TT).get (Fin.ext h))
  exact cdist_next_pos_and_le_of_strictMono (evenTops TT) (ev_mono TT) j _ m rfl hmj

theorem mem_dists {TT : Finset (Fin n')} {j : Fin (numSeg TT)} {d : ℕ} :
    d ∈ segDists TT j ↔ ∃ s, (s ∈ TT ∧ ¬ Even s.val ∧ 0 < cdist (segStart TT j) s ∧
      cdist (segStart TT j) s < segG TT j) ∧ cdist (segStart TT j) s = d := by
  simp only [segDists, Finset.mem_sort, Finset.mem_image, Finset.mem_filter]

theorem get_spec (TT : Finset (Fin n')) (j : Fin (numSeg TT)) (i : Fin (segS TT j)) :
    ∃ s, (s ∈ TT ∧ ¬ Even s.val ∧ 0 < cdist (segStart TT j) s ∧
      cdist (segStart TT j) s < segG TT j) ∧ cdist (segStart TT j) s = (segDists TT j).get i := mem_dists.1 (List.get_mem _ _)

theorem pos_mem (TT : Finset (Fin n')) (j : Fin (numSeg TT)) (i : Fin (segS TT j)) :
    segPos TT j i ∈ TT ∧ ¬ Even (segPos TT j i).val := by
  obtain ⟨s, hs, hd⟩ := get_spec TT j i
  unfold segPos
  rw [← hd, posAdd_cdist]
  exact ⟨hs.1, hs.2.1⟩

theorem pos_ne_start (TT : Finset (Fin n')) (j : Fin (numSeg TT)) (i : Fin (segS TT j)) :
    segPos TT j i ≠ segStart TT j := by
  obtain ⟨s, hs, hd⟩ := get_spec TT j i
  intro h
  unfold segPos at h
  rw [← hd, posAdd_cdist] at h
  have h0 := hs.2.2.1
  rw [h] at h0
  simp [cdist] at h0

theorem dist_pos_lt (TT : Finset (Fin n')) (j : Fin (numSeg TT)) (i : Fin (segS TT j)) :
    0 < (segDists TT j).get i ∧ (segDists TT j).get i < segG TT j := by
  obtain ⟨s, hs, hd⟩ := get_spec TT j i
  rw [← hd]
  exact ⟨hs.2.2.1, hs.2.2.2⟩

theorem dist_odd (hn : Even n') (TT : Finset (Fin n')) (j : Fin (numSeg TT)) (i : Fin (segS TT j)) :
    Odd ((segDists TT j).get i) := by
  obtain ⟨s, hs, hd⟩ := get_spec TT j i
  rw [← hd]
  have he := (start_mem TT j).2
  have ho := hs.2.1
  rw [Nat.even_iff] at he ho hn
  rw [Nat.odd_iff]
  rcases cd_cases (segStart TT j) s with ⟨h, e⟩ | ⟨h, e⟩ <;> rw [e] <;> omega

theorem segG_even (hn : Even n') (TT : Finset (Fin n')) (j : Fin (numSeg TT)) : Even (segG TT j) := by
  have h1 := (start_mem TT j).2
  have h2 := (next_mem TT j).2
  rw [Nat.even_iff] at h1 h2 hn
  unfold segG
  split_ifs with h
  · exact Nat.even_iff.2 hn
  · rw [Nat.even_iff]
    rcases cd_cases (segStart TT j) (segNext TT j) with ⟨h', e⟩ | ⟨h', e⟩ <;> rw [e] <;> omega

theorem dist_strictMono (TT : Finset (Fin n')) (j : Fin (numSeg TT)) : StrictMono (segDists TT j).get := (Finset.sortedLT_sort _).strictMono_get

theorem filter_len_iff {n : ℕ} (P : Fin n → Prop) [DecidablePred P] (hP : ∀ i i' : Fin n, i ≤ i' → P i' → P i)
    (i : Fin n) : (i : ℕ) < ((List.finRange n).filter (fun i => decide (P i))).length ↔ P i := by
  have hc : ((List.finRange n).filter (fun i => decide (P i))).length =
      (Finset.univ.filter P).card := by
    rw [Fin.univ_def]
    rfl
  rw [hc]
  constructor
  · intro hlt
    by_contra hn
    have hsub : Finset.univ.filter P ⊆ Finset.Iio i := by
      intro x hx
      rw [Finset.mem_filter] at hx
      rw [Finset.mem_Iio]
      by_contra hge
      exact hn (hP i x (not_lt.1 hge) hx.2)
    have := Finset.card_le_card hsub
    rw [Fin.card_Iio] at this
    omega
  · intro hPi
    have hsub : Finset.Iic i ⊆ Finset.univ.filter P := by
      intro x hx
      rw [Finset.mem_Iic] at hx
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hP x i hx hPi⟩
    have := Finset.card_le_card hsub
    rw [Fin.card_Iic] at this
    omega

theorem sigma_iff (p : ℕ) (hp : 1 < p) (TT : Finset (Fin n')) (bT : Fin n' → ℕ) (a : ℕ) (b' Y La E0 : ℝ)
    (j : Fin (numSeg TT)) (i : Fin (segS TT j)) :
    (i : ℕ) < (segData p TT bT a b' Y La E0 j).sigma ↔ (p : ℝ) ^ ((segDists TT j).get i) < (a : ℝ) / b' := by
  show (i : ℕ) < ((List.finRange (segS TT j)).filter
    (fun i => decide ((p : ℝ) ^ ((segDists TT j).get i) < (a : ℝ) / b'))).length ↔ _
  refine filter_len_iff (fun i => (p : ℝ) ^ ((segDists TT j).get i) < (a : ℝ) / b') ?_ i
  intro i i' hii' h
  refine lt_of_le_of_lt ?_ h
  exact pow_le_pow_right₀ (by exact_mod_cast hp.le) ((dist_strictMono TT j).monotone hii')

def oddSet (TT : Finset (Fin n')) (j : Fin (numSeg TT)) : Finset (Fin n') :=
  TT.filter (fun s => ¬ Even s.val ∧ 0 < cdist (segStart TT j) s ∧ cdist (segStart TT j) s < segG TT j)

theorem segS_le (TT : Finset (Fin n')) (j : Fin (numSeg TT)) : segS TT j ≤ (oddSet TT j).card := by
  simp only [segS, segDists, Finset.length_sort]
  exact Finset.card_image_le

private lemma cdist_lt_segStart_of_mem_oddSet_of_ne (TT : Finset (Fin n')) (j j' : Fin (numSeg TT)) (h : j ≠ j') {s : Fin n'}
    (hs : s ∈ oddSet TT j) : cdist (segStart TT j) s < cdist (segStart TT j) (segStart TT j') := by
  have hne : segStart TT j' ≠ segStart TT j := (ev_mono TT).injective.ne (Ne.symm h)
  obtain ⟨hpos, hle⟩ := next_min TT j (segStart TT j') (start_mem TT j').1 (start_mem TT j').2 hne
  have hg : segG TT j = cdist (segStart TT j) (segNext TT j) := by
    simp only [segG, if_neg hpos.ne']
  have := (Finset.mem_filter.1 hs).2.2.2
  omega

theorem oddSet_disj (TT : Finset (Fin n')) (j j' : Fin (numSeg TT)) (h : j ≠ j') :
    Disjoint (oddSet TT j) (oddSet TT j') := by
  rw [Finset.disjoint_left]
  intro s hs hs'
  have h1 := cdist_lt_segStart_of_mem_oddSet_of_ne TT j j' h hs
  have h2 := cdist_lt_segStart_of_mem_oddSet_of_ne TT j' j (Ne.symm h) hs'
  have p1 := (Finset.mem_filter.1 hs).2.2.1
  have p2 := (Finset.mem_filter.1 hs').2.2.1
  have hne : (segStart TT j).val ≠ (segStart TT j').val := fun e =>
    (ev_mono TT).injective.ne h (Fin.ext e)
  have ha := (segStart TT j).isLt
  have hb := (segStart TT j').isLt
  have hsl := s.isLt
  rcases cd_cases (segStart TT j) s with ⟨_, e1⟩ | ⟨_, e1⟩ <;>
  rcases cd_cases (segStart TT j') s with ⟨_, e2⟩ | ⟨_, e2⟩ <;>
  rcases cd_cases (segStart TT j) (segStart TT j') with ⟨_, e3⟩ | ⟨_, e3⟩ <;>
  rcases cd_cases (segStart TT j') (segStart TT j) with ⟨_, e4⟩ | ⟨_, e4⟩ <;>
  omega

theorem sum_segS (TT : Finset (Fin n')) (_h2 : 2 ≤ numSeg TT) :
    (∑ j, segS TT j) + numSeg TT ≤ TT.card := by
  have hdisj : Disjoint (Finset.univ.biUnion (oddSet TT)) (TT.filter (fun s => Even s.val)) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.1 hx
    exact (Finset.mem_filter.1 hj).2.1 (Finset.mem_filter.1 hx').2
  calc (∑ j, segS TT j) + numSeg TT
      ≤ (∑ j, (oddSet TT j).card) + (TT.filter (fun s => Even s.val)).card :=
        add_le_add (Finset.sum_le_sum fun j _ => segS_le TT j) (numSeg_eq TT).le
    _ = (Finset.univ.biUnion (oddSet TT)).card + (TT.filter (fun s => Even s.val)).card := by
        rw [Finset.card_biUnion]
        intro j _ j' _ h
        exact oddSet_disj TT j j' h
    _ = (Finset.univ.biUnion (oddSet TT) ∪ TT.filter (fun s => Even s.val)).card :=
        (Finset.card_union_of_disjoint hdisj).symm
    _ ≤ TT.card := by
        apply Finset.card_le_card
        apply Finset.union_subset
        · intro x hx
          obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.1 hx
          exact (Finset.mem_filter.1 hj).1
        · exact Finset.filter_subset _ _

theorem segment_statement_holds (D : Formalism.BasicNotions.D7) (C0 CE1 CE2 : ℝ) : PointsLemma D C0 CE1 CE2 := by
  intro X _ O _ _ _ j aT' m hne haT
  have h1 : segATop X.TT aT' j = segATop X.TT X.aT j :=
    funext fun i => haT _ (pos_ne_start _ _ _)
  have h2 : segAPlus X.TT aT' j = segAPlus X.TT X.aT j := haT _ hne
  rw [h1, h2]
  rfl

end Formalism.MainNotions.ColumnSystems.Pf
