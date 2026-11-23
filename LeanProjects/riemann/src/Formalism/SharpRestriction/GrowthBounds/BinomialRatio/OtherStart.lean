import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.SegmentStatementHolds

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G

variable {n' : ℕ}

def rot (n : ℕ) (j : Fin n) : Fin n := ⟨(j.val + 1) % n, Nat.mod_lt _ j.pos⟩

theorem rot_val (n : ℕ) (j : Fin n) :
    (j.val + 1 < n ∧ (rot n j).val = j.val + 1) ∨ (j.val + 1 = n ∧ (rot n j).val = 0) := by
  have hj := j.isLt
  by_cases h : j.val + 1 < n
  · left
    exact ⟨h, Nat.mod_eq_of_lt h⟩
  · right
    have e : j.val + 1 = n := by omega
    refine ⟨e, ?_⟩
    show (j.val + 1) % n = 0
    rw [e, Nat.mod_self]

theorem rot_inj (n : ℕ) : Function.Injective (rot n) := by
  intro j j' h
  have h' := congrArg Fin.val h
  have a := rot_val n j
  have b := rot_val n j'
  apply Fin.ext
  omega

theorem rot_bij (n : ℕ) : Function.Bijective (rot n) := Finite.injective_iff_bijective.mp (rot_inj n)

theorem next_eq (TT : Finset (Fin n')) (j : Fin (numSeg TT)) : segNext TT j = segStart TT (rot _ j) := rfl

theorem prod_next (TT : Finset (Fin n')) (h : Fin n' → ℝ) :
    ∏ j, h (segNext TT j) = ∏ j, h (segStart TT j) :=
  (rot_bij (numSeg TT)).prod_comp (fun j => h (segStart TT j))

theorem other_start (TT : Finset (Fin n')) (h2 : 2 ≤ numSeg TT) (j : Fin (numSeg TT)) :
    ∃ e, e ∈ TT ∧ Even e.val ∧ e ≠ segStart TT j := by
  by_cases h0 : j.val = 0
  · refine ⟨segStart TT ⟨1, by omega⟩, (start_mem TT _).1, (start_mem TT _).2, fun e => ?_⟩
    have := congrArg Fin.val ((ev_mono TT).injective e)
    simp at this
    omega
  · refine ⟨segStart TT ⟨0, by omega⟩, (start_mem TT _).1, (start_mem TT _).2, fun e => ?_⟩
    have := congrArg Fin.val ((ev_mono TT).injective e)
    simp at this
    omega

theorem segG_eq (TT : Finset (Fin n')) (h2 : 2 ≤ numSeg TT) (j : Fin (numSeg TT)) :
    segG TT j = cdist (segStart TT j) (segNext TT j) ∧ 0 < cdist (segStart TT j) (segNext TT j) := by
  obtain ⟨e, he, hev, hne⟩ := other_start TT h2 j
  obtain ⟨m1, -⟩ := next_min TT j e he hev hne
  refine ⟨?_, m1⟩
  unfold segG
  rw [if_neg (by omega)]

theorem sum_segG (TT : Finset (Fin n')) (h2 : 2 ≤ numSeg TT) : ∑ j, segG TT j = n' := by
  have key : ∀ j : Fin (numSeg TT), (segG TT j : ℤ) =
      ((segStart TT (rot _ j)).val : ℤ) - ((segStart TT j).val : ℤ) +
        (if j = ⟨numSeg TT - 1, by omega⟩ then (n' : ℤ) else 0) := by
    intro j
    obtain ⟨g, g0⟩ := segG_eq TT h2 j
    rw [g, next_eq] at *
    have c := cd_cases (segStart TT j) (segStart TT (rot _ j))
    have l1 := (segStart TT j).isLt
    have l2 := (segStart TT (rot _ j)).isLt
    rcases rot_val _ j with ⟨r1, r2⟩ | ⟨r1, r2⟩
    · have hlt : (segStart TT j).val < (segStart TT (rot _ j)).val :=
        ev_mono TT (Fin.lt_def.mpr (by omega))
      have hne : j ≠ ⟨numSeg TT - 1, by omega⟩ := by
        intro e
        have := congrArg Fin.val e
        simp at this
        omega
      rw [if_neg hne]
      omega
    · have hlt : (segStart TT (rot _ j)).val < (segStart TT j).val :=
        ev_mono TT (Fin.lt_def.mpr (by omega))
      have he : j = ⟨numSeg TT - 1, by omega⟩ := by
        apply Fin.ext
        show j.val = numSeg TT - 1
        omega
      rw [if_pos he]
      omega
  have hs : (∑ j, ((segStart TT (rot _ j)).val : ℤ)) = ∑ j, ((segStart TT j).val : ℤ) :=
    (rot_bij (numSeg TT)).sum_comp (fun j => ((segStart TT j).val : ℤ))
  have : ((∑ j, segG TT j : ℕ) : ℤ) = (n' : ℤ) := by
    push_cast
    rw [Finset.sum_congr rfl fun j _ => key j, Finset.sum_add_distrib, Finset.sum_sub_distrib, hs]
    simp
  exact_mod_cast this

theorem prod_starts (TT : Finset (Fin n')) (h : Fin n' → ℝ) :
    ∏ j, h (segStart TT j) = ∏ s ∈ TT.filter (fun s => Even s.val), h s := by
  refine Finset.prod_nbij (fun j => segStart TT j) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro j _
    exact Finset.mem_filter.mpr (start_mem TT j)
  · intro j _ j' _ e
    exact (ev_mono TT).injective e
  · intro s hs
    have hs' := Finset.mem_filter.mp (Finset.mem_coe.mp hs)
    obtain ⟨k, hk⟩ := List.mem_iff_get.mp ((ev_mem TT s).mpr hs')
    exact ⟨k, Finset.mem_coe.mpr (Finset.mem_univ _), hk⟩

theorem pos_spec (TT : Finset (Fin n')) (j : Fin (numSeg TT)) (i : Fin (segS TT j)) :
    segPos TT j i ∈ oddSet TT j ∧ cdist (segStart TT j) (segPos TT j i) = (segDists TT j).get i := by
  obtain ⟨s, hs, h5⟩ := get_spec TT j i
  have : segPos TT j i = s := by
    unfold segPos
    rw [← h5, posAdd_cdist]
  rw [this]
  exact ⟨Finset.mem_filter.mpr hs, h5⟩

theorem prod_pos (TT : Finset (Fin n')) (j : Fin (numSeg TT)) (h : Fin n' → ℝ) :
    ∏ i, h (segPos TT j i) = ∏ s ∈ oddSet TT j, h s := by
  refine Finset.prod_nbij (fun i => segPos TT j i) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro i _
    exact (pos_spec TT j i).1
  · intro i _ i' _ e
    have e' : segPos TT j i = segPos TT j i' := e
    have h1 := (pos_spec TT j i).2
    have h2 := (pos_spec TT j i').2
    rw [e'] at h1
    exact (dist_strictMono TT j).injective (h1.symm.trans h2)
  · intro s hs
    have hs' := Finset.mem_filter.mp (Finset.mem_coe.mp hs)
    have hd : cdist (segStart TT j) s ∈ segDists TT j := mem_dists.mpr ⟨s, hs', rfl⟩
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hd
    refine ⟨i, Finset.mem_coe.mpr (Finset.mem_univ _), ?_⟩
    show segPos TT j i = s
    unfold segPos
    rw [hi, posAdd_cdist]

theorem odd_covered (TT : Finset (Fin n')) (h2 : 2 ≤ numSeg TT) (s : Fin n') (hs : s ∈ TT) (ho : ¬ Even s.val) :
    ∃ j, s ∈ oddSet TT j := by
  have hne : (TT.filter (fun x => Even x.val)).Nonempty :=
    ⟨segStart TT ⟨0, by omega⟩, Finset.mem_filter.mpr (start_mem TT _)⟩
  obtain ⟨x, hx, hmin⟩ := Finset.exists_min_image (TT.filter (fun x => Even x.val)) (fun x => cdist x s) hne
  have hx' := Finset.mem_filter.mp hx
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp ((ev_mem TT x).mpr hx')
  have hj' : segStart TT j = x := hj
  refine ⟨j, Finset.mem_filter.mpr ⟨hs, ho, ?_, ?_⟩⟩
  · rw [hj']
    have c := cd_cases x s
    have l1 := x.isLt
    have l2 := s.isLt
    have hxs : x.val ≠ s.val := by
      intro e
      rw [← e] at ho
      exact ho hx'.2
    omega
  · obtain ⟨g, g0⟩ := segG_eq TT h2 j
    rw [g]
    by_contra hcon
    have hy := hmin (segNext TT j) (Finset.mem_filter.mpr (next_mem TT j))
    rw [hj'] at g0 hcon
    have c1 := cd_cases x s
    have c2 := cd_cases x (segNext TT j)
    have c3 := cd_cases (segNext TT j) s
    have l1 := x.isLt
    have l2 := s.isLt
    have l3 := (segNext TT j).isLt
    omega

theorem biUnion_odd (TT : Finset (Fin n')) (h2 : 2 ≤ numSeg TT) :
    Finset.univ.biUnion (oddSet TT) = TT.filter (fun s => ¬ Even s.val) := by
  ext s
  constructor
  · intro hs
    obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.mp hs
    obtain ⟨a0, a1, -⟩ := Finset.mem_filter.mp hj
    exact Finset.mem_filter.mpr ⟨a0, a1⟩
  · intro hs
    obtain ⟨a0, a1⟩ := Finset.mem_filter.mp hs
    obtain ⟨j, hj⟩ := odd_covered TT h2 s a0 a1
    exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, hj⟩

theorem prod_tops (TT : Finset (Fin n')) (h2 : 2 ≤ numSeg TT) (h : Fin n' → ℝ) :
    ∏ s ∈ TT, h s = ∏ j, (h (segStart TT j) * ∏ i, h (segPos TT j i)) := by
  rw [Finset.prod_mul_distrib, prod_starts, Finset.prod_congr rfl fun j _ => prod_pos TT j h,
    ← Finset.prod_biUnion (fun j _ j' _ hjj => oddSet_disj TT j j' hjj), biUnion_odd TT h2,
    Finset.prod_filter_mul_prod_filter_not]

end Formalism.MainNotions.ColumnSystems.Pf
