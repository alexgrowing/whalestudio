import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.TopWeightFalseZeroEqOne

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

section Eval

variable {C0 CE1 CE2 mu : ℝ} {X : Loc} [NeZero X.m] {β : GlobalTheory X}

theorem tg_odd_ne_end (X : Loc) (j j' : Fin (numSeg X.TT)) (i : Fin (segS X.TT j)) : topOdd X j i ≠ topEnd X j' := by
  intro h
  have e : segPos X.TT j i = segNext X.TT j' := congrArg Subtype.val h
  exact (pos_mem X.TT j i).2 (e ▸ (next_mem X.TT j').2)

theorem tg_eval_odd (L : LvDat C0 CE1 CE2 mu X β) (ju : ∀ j, Fin (X.seg C0 CE1 CE2 j).t → ℕ)
    (du : ∀ j, Fin (2 * segS X.TT j + 1) → ℕ) (A : MonH X) (j : Fin (numSeg X.TT)) (i0 : Fin (segS X.TT j)) (b0 : Bool) :
    ∑ j', (tgHD L j' (ju j') (du j') (wLet X (topOdd X j i0, b0)) + tgWM X j' A (wLet X (topOdd X j i0, b0))) =
      (X.seg C0 CE1 CE2 j).P X.p i0 * (jE (X.seg C0 CE1 CE2 j) (ju j) i0.val + du j (if b0 then chW i0 else chE i0)) +
        ∑ c, A ((topOdd X j i0, b0), c) := by
  classical
  have hoth : ∀ j', j' ≠ j → ∀ (i' : Fin (segS X.TT j')) (b : Bool) (c : Fin (X.m + 1)),
      wLet X (topOdd X j i0, b0) ((topOdd X j' i', b), c) = 0 := by
    intro j' hne i' b c
    unfold wLet
    rw [if_neg]
    intro h
    have h1 : topOdd X j' i' = topOdd X j i0 := congrArg Prod.fst h
    have h2 := tgTop_inj X (a₁ := ⟨j', some i'⟩) (a₂ := ⟨j, some i0⟩) h1
    exact hne (congrArg Sigma.fst h2)
  have hend : ∀ j' (b : Bool) (c : Fin (X.m + 1)), wLet X (topOdd X j i0, b0) ((topEnd X j', b), c) = 0 := by
    intro j' b c
    unfold wLet
    rw [if_neg]
    intro h
    exact tg_odd_ne_end X j j' i0 (congrArg Prod.fst h).symm
  have hsame : ∀ (i : Fin (segS X.TT j)) (b : Bool) (c : Fin (X.m + 1)),
      wLet X (topOdd X j i0, b0) ((topOdd X j i, b), c) = if i = i0 ∧ b = b0 then 1 else 0 := by
    intro i b c
    unfold wLet
    simp only [Prod.mk.injEq, (topOdd_inj X j).eq_iff]
  rw [Finset.sum_eq_single j]
  · unfold tgHD tgWM
    simp only [hend, hsame, mul_zero, add_zero, Finset.sum_const_zero]
    rw [Finset.sum_eq_single i0, Finset.sum_eq_single i0]
    · cases b0 <;> simp
    · intro i _ hi; simp [hi]
    · intro h; exact absurd (Finset.mem_univ _) h
    · intro i _ hi; simp [hi]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro j' _ hj'
    unfold tgHD tgWM
    simp only [hoth j' hj', hend, mul_zero, add_zero, Finset.sum_const_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem tg_eval_end (L : LvDat C0 CE1 CE2 mu X β) (ju : ∀ j, Fin (X.seg C0 CE1 CE2 j).t → ℕ)
    (du : ∀ j, Fin (2 * segS X.TT j + 1) → ℕ) (A : MonH X) (j : Fin (numSeg X.TT)) :
    ∑ j', (tgHD L j' (ju j') (du j') (wLet X (topEnd X j, true)) + tgWM X j' A (wLet X (topEnd X j, true))) =
      L.jp j + du j (chU _) + ∑ c, A ((topEnd X j, true), c) := by
  classical
  have hodd : ∀ j' (i' : Fin (segS X.TT j')) (b : Bool) (c : Fin (X.m + 1)),
      wLet X (topEnd X j, true) ((topOdd X j' i', b), c) = 0 := by
    intro j' i' b c
    unfold wLet
    rw [if_neg]
    intro h
    exact tg_odd_ne_end X j' j i' (congrArg Prod.fst h)
  have hend : ∀ j' (b : Bool) (c : Fin (X.m + 1)),
      wLet X (topEnd X j, true) ((topEnd X j', b), c) = if j' = j ∧ b = true then 1 else 0 := by
    intro j' b c
    unfold wLet
    have e : topEnd X j' = topEnd X j ↔ j' = j := by
      constructor
      · intro h
        exact congrArg Sigma.fst (tgTop_inj X (a₁ := ⟨j', none⟩) (a₂ := ⟨j, none⟩) h)
      · intro h; rw [h]
    simp only [Prod.mk.injEq, e]
  rw [Finset.sum_eq_single j]
  · unfold tgHD tgWM
    simp [hodd, hend]
  · intro j' _ hj'
    unfold tgHD tgWM
    simp [hodd, hend, hj']
  · intro h; exact absurd (Finset.mem_univ _) h

end Eval

theorem tcoreAt_of_seg {C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ} (h : SegCoreAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc) :
    TCoreAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc := by
  intro X _ _ O _ _ _ _ S hSq hD hH hc mm hmm n hn1 hnc β hβ L Std hStd e he1 hen ju hju Gu du hGI hGP hdu hY A hA1 hA2 hA3
    hPol hnd
  classical
  have h2 : 2 ≤ numSeg X.TT := hH.1.2.2.2.1
  by_cases hT0 : (∏ j, L.head O j (ju j) (Gu j)) * monomial A 1 = 0
  · rw [hT0]; exact Submodule.zero_mem _
  have hS := tg_std_eq O h2 L Std hStd
  have sv : ∀ (pl : TgPlace X) (b : Bool) (c : Fin (X.m + 1)), Std ((tgTop X pl, b), c) = tgStdE L pl b c := by
    intro pl b c
    rw [hS]
    exact tgStdX_at h2 L pl b c
  have hsplit : (∏ j, L.head O j (ju j) (Gu j)) * monomial A 1 = ∏ j, (L.head O j (ju j) (Gu j) * segMon O X j A) := by
    rw [tg_mono_split O X h2, Finset.prod_mul_distrib]
  have hwh : ∀ ω : (X.TT × Bool) × Fin (X.m + 1) → ℕ, (∀ x (c c' : Fin X.m), ω (x, c.succ) = ω (x, c'.succ)) →
      (∀ j (i : Fin (segS X.TT j)), ω ((topOdd X j i, true), 0) + ω ((topOdd X j i, false), 0) =
        ω ((topOdd X j i, true), Fin.succ 0) + ω ((topOdd X j i, false), Fin.succ 0)) →
      (∀ j, ω ((topEnd X j, true), 0) + ω ((topEnd X j, false), 0) =
        ω ((topEnd X j, true), Fin.succ 0) + ω ((topEnd X j, false), Fin.succ 0)) →
      IsWeightedHomogeneous ω ((∏ j, L.head O j (ju j) (Gu j)) * monomial A 1)
        (∑ j, (tgHD L j (ju j) (du j) ω + tgWM X j A ω)) := by
    intro ω a1 a2 a3
    rw [hsplit]
    exact IsWeightedHomogeneous.prod _ _ _ fun j _ =>
      (tg_head_wh O L j (ju j) (Gu j) (du j) (hGP j) ω a1 (a2 j) (a3 j)).mul (tg_segMon_wh O j A ω)
  obtain ⟨m0, hm0⟩ := MvPolynomial.ne_zero_iff.1 hT0
  have hdeg : ∀ x : X.TT × Bool, ∑ j, (tgHD L j (ju j) (du j) (wLet X x) + tgWM X j A (wLet X x)) =
      hhDegs X.TT X.aT X.bT x := by
    intro x
    have a1 := hwh (wLet X x) (fun _ _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) hm0
    have a2 : multideg m0 x = hhDegs X.TT X.aT X.bT x :=
      ((mem_restrictSupport_iff _).1 hPol) (Finset.mem_coe.2 (mem_support_iff.2 hm0)) x
    rw [← a1, weight_wLet, a2]
  have hA0 : ∀ j, A ((topEnd X j, false), 0) = 0 := by
    intro j
    rw [hA3 j 0]
    exact sv ⟨j, none⟩ false 0
  have hnu : ∑ j, nuSeg C0 CE1 CE2 X j (ju j) (L.jp j) (du j) A ≤ ordFam C0 CE1 CE2 X β + e := by
    have a1 := hwh (tgWN X)
      (fun x c c' => by obtain ⟨t, b⟩ := x; cases b <;> simp [tgWN_ts, tgWN_fs])
      (fun j i => by rw [tgWN_true_zero_eq_zero, top_weight_false_zero_eq_one, tgWN_ts, tgWN_fs])
      (fun j => by rw [tgWN_true_zero_eq_zero, top_weight_false_zero_eq_one, tgWN_ts, tgWN_fs]) hm0
    have a2 := hnd m0 (mem_support_iff.2 hm0)
    rw [← weight_tgWN, a1] at a2
    refine le_trans (le_of_eq ?_) a2
    refine Finset.sum_congr rfl fun j _ => ?_
    have t := tg_nd_eval L j (ju j) (du j) A
    rw [hA0 j, add_zero] at t
    exact t.symm
  have key : ∀ j, ∃ b' : SegBlock (segS X.TT j) X.m,
        BLk C0 Cde CE1 CE2 X (((X.c - (n - e) : ℕ) : ℝ) * ka1 X) j b' ∧
        blockOrd X.p (X.seg C0 CE1 CE2 j) b' = nuSeg C0 CE1 CE2 X j (ju j) (L.jp j) (du j) A ∧
        ∃ u ∈ (blockData X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j)
            (mm + ((n - e : ℕ) : ℝ) * ka1 X) b').SSZ O (r := X.m),
          L.head O j (ju j) (Gu j) * segMon O X j A = ioBlock (KK O) X.p C0 CE1 CE2 X j b' u := by
    intro j
    refine h X O S hSq hD hH hc mm hmm n hn1 hnc β hβ L e he1 hen j (ju j) (hju j) (Gu j) (du j) (hGI j) (hGP j) (hdu j)
      (hY j) A ?_ ?_ ?_ ?_ (hA0 j) ?_ ?_ ?_ ?_
    · intro i
      have a := hA1 (topOdd X j i, true)
      have b : Std ((topOdd X j i, true), 0) - A ((topOdd X j i, true), 0) ≤
          ∑ c, (Std ((topOdd X j i, true), c) - A ((topOdd X j i, true), c)) :=
        Finset.single_le_sum (f := fun c => Std ((topOdd X j i, true), c) - A ((topOdd X j i, true), c))
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ 0)
      have v : Std ((topOdd X j i, true), 0) = (β j).rz i 0 + (X.seg C0 CE1 CE2 j).P X.p i *
          (coarseA X.p (X.seg C0 CE1 CE2 j) (β j) i -
            (if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then (β j).w i else (β j).o i)) := by
        have := sv ⟨j, some i⟩ true 0
        simpa [tgStdE, tgTop] using this
      omega
    · intro i
      have a := hA2 (topOdd X j i, true)
      rw [Fin.sum_univ_succ] at a
      have v : ∀ c : Fin X.m, Std ((topOdd X j i, true), c.succ) = (β j).rz i c.succ := by
        intro c
        have := sv ⟨j, some i⟩ true c.succ
        simpa [tgStdE, tgTop, Fin.succ_ne_zero] using this
      simp only [v] at a
      omega
    · intro i
      have a := hA2 (topOdd X j i, false)
      have b : A ((topOdd X j i, false), 0) - Std ((topOdd X j i, false), 0) ≤
          ∑ c, (A ((topOdd X j i, false), c) - Std ((topOdd X j i, false), c)) :=
        Finset.single_le_sum (f := fun c => A ((topOdd X j i, false), c) - Std ((topOdd X j i, false), c))
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ 0)
      have v : Std ((topOdd X j i, false), 0) = (β j).ry i 0 + (X.seg C0 CE1 CE2 j).P X.p i *
          (if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then (β j).sg i else 0) := by
        have := sv ⟨j, some i⟩ false 0
        simpa [tgStdE, tgTop] using this
      omega
    · have a := hA2 (topEnd X j, true)
      rw [Fin.sum_univ_succ] at a
      have v : ∀ c : Fin X.m, Std ((topEnd X j, true), c.succ) = 0 := by
        intro c
        have := sv ⟨j, none⟩ true c.succ
        simpa [tgStdE, tgTop, Fin.succ_ne_zero] using this
      simp only [v, Nat.sub_zero] at a
      omega
    · intro c
      rw [hA3 j c.succ]
      exact sv ⟨j, none⟩ false c.succ
    · intro i
      have a := hdeg (topOdd X j i, true)
      rw [tg_eval_odd L ju du A j i true] at a
      have hb : hhDegs X.TT X.aT X.bT (topOdd X j i, true) = (X.seg C0 CE1 CE2 j).bTop i := by
        show hhDeg X.aT X.bT (segPos X.TT j i) true = X.bT (segPos X.TT j i)
        unfold hhDeg
        rw [if_pos rfl, if_neg (pos_mem X.TT j i).2]
      rw [hb] at a
      exact a
    · intro i
      have a := hdeg (topOdd X j i, false)
      rw [tg_eval_odd L ju du A j i false] at a
      have hb : hhDegs X.TT X.aT X.bT (topOdd X j i, false) = segATop X.TT X.aT j i := by
        show hhDeg X.aT X.bT (segPos X.TT j i) false = X.aT (segPos X.TT j i)
        unfold hhDeg
        rw [if_neg (by simp), if_neg (pos_mem X.TT j i).2]
      rw [hb] at a
      exact a
    · have a := hdeg (topEnd X j, true)
      rw [tg_eval_end L ju du A j] at a
      have hb : hhDegs X.TT X.aT X.bT (topEnd X j, true) = segAPlus X.TT X.aT j := by
        show hhDeg X.aT X.bT (segNext X.TT j) true = X.aT (segNext X.TT j)
        unfold hhDeg
        rw [if_pos rfl, if_pos (next_mem X.TT j).2]
      rw [hb] at a
      exact a
  choose β' hBL hord u hu hEq using key
  rw [hsplit, Finset.prod_congr rfl fun j _ => hEq j]
  show symFam (KK O) X.p C0 CE1 CE2 X β' u ∈ _
  refine symFam_span β' (fun j => genSet O (r := X.m)
    (blockData X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j)
      (mm + ((n - e : ℕ) : ℝ) * ka1 X) (β' j))) _ ?_ u (fun j => hu j)
  intro s hs
  refine Submodule.subset_span ⟨β', hBL, ?_, s, hs, rfl⟩
  unfold ordFam
  rw [Finset.sum_congr rfl fun j _ => hord j]
  exact hnu

theorem restTCore_of_seg (h : RestSegCore) : RestTCore :=
  TransportedAlt.mono (fun _ _ _ _ _ _ _ _ _ _ h => tcoreAt_of_seg h) h

end Formalism.MainNotions.ColumnSystems.Pf
