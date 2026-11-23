import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.ColsS
import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.ColXCnt
import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.ColXSeg

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf.GenusGluing

open Formalism.MainNotions.G MvPolynomial Formalism.MainNotions.LemmaBAlt Formalism.MainNotions.ColumnSystems.Pf.Col

theorem floor_cap {s r : ℕ} (p : ℕ) (S : SegData s) (b : SegBlock s r) (mu : ℝ) (L0 : ℕ)
    (hL : ∀ l : Fin s, (l : ℕ) < S.sigma → (l : ℕ) < L0)
    (hw : ∀ l : Fin s, (l : ℕ) < S.sigma → b.w l ≤ coarseA p S b l)
    (ho : ∀ l : Fin s, S.sigma ≤ (l : ℕ) → b.o l ≤ coarseA p S b l) :
    ⌊((cap p S b L0 : ℤ) : ℝ) - mu⌋ =
      ⌊((S.A0 p : ℤ) : ℝ) - mu⌋ - (∑ l : Fin s, (if (l : ℕ) < S.sigma then (b.sg l : ℤ) else 0)) +
        ∑ l : Fin s, (if 2 * (l : ℕ) + 2 ≤ 2 * L0 + 1 then
          ((coarseA p S b l - (if (l : ℕ) < S.sigma then b.w l else b.o l) : ℕ) : ℤ) else 0) := by
  have hD : (∑ i : Fin s, if (i : ℕ) < L0 then ((coarseA p S b i : ℤ) - (oEff S b i : ℤ)) else 0) =
      (∑ l : Fin s, (if 2 * (l : ℕ) + 2 ≤ 2 * L0 + 1 then
          ((coarseA p S b l - (if (l : ℕ) < S.sigma then b.w l else b.o l) : ℕ) : ℤ) else 0)) -
      ∑ l : Fin s, (if (l : ℕ) < S.sigma then (b.sg l : ℤ) else 0) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    unfold oEff
    by_cases h1 : (l : ℕ) < S.sigma
    · have h2 := hL l h1
      have h3 : 2 * (l : ℕ) + 2 ≤ 2 * L0 + 1 := by omega
      simp only [if_pos h1, if_pos h2, if_pos h3]
      rw [Nat.cast_sub (hw l h1)]
      push_cast; ring
    · by_cases h2 : (l : ℕ) < L0
      · have h3 : 2 * (l : ℕ) + 2 ≤ 2 * L0 + 1 := by omega
        simp only [if_neg h1, if_pos h2, if_pos h3]
        rw [Nat.cast_sub (ho l (not_lt.1 h1))]
        ring
      · have h3 : ¬ 2 * (l : ℕ) + 2 ≤ 2 * L0 + 1 := by omega
        simp only [if_neg h1, if_neg h2, if_neg h3]
        ring
  unfold cap
  rw [hD]
  generalize (∑ l : Fin s, (if 2 * (l : ℕ) + 2 ≤ 2 * L0 + 1 then
          ((coarseA p S b l - (if (l : ℕ) < S.sigma then b.w l else b.o l) : ℕ) : ℤ) else 0)) = P
  generalize (∑ l : Fin s, (if (l : ℕ) < S.sigma then (b.sg l : ℤ) else 0)) = Q
  have e : (((S.A0 p + (P - Q) : ℤ)) : ℝ) - mu = (((S.A0 p : ℤ) : ℝ) - mu) + ((P - Q : ℤ) : ℝ) := by
    push_cast; ring
  rw [e, Int.floor_add_intCast]; ring

theorem first_row_le {n N : ℕ} [NeZero n] {Lt : Letters (Fin N)} {B : Fin N → ℕ} (P : PPath n N Lt B)
    (t : Fin (N + 1)) :
    P.mu t 0 ≤ ∑ a : Fin N, if a.val < t.val ∧ Lt.vec a = true then (B a : ℤ) else 0 := by
  induction t using Fin.induction with
  | zero => rw [P.zero]; simp
  | succ i ih =>
    have hs := P.step i
    have hsplit : (∑ a : Fin N, if a.val < i.succ.val ∧ Lt.vec a = true then (B a : ℤ) else 0) =
        (∑ a : Fin N, if a.val < i.castSucc.val ∧ Lt.vec a = true then (B a : ℤ) else 0) +
          (if Lt.vec i = true then (B i : ℤ) else 0) := by
      have e : (if Lt.vec i = true then (B i : ℤ) else 0) =
          ∑ a : Fin N, if a = i then (if Lt.vec a = true then (B a : ℤ) else 0) else 0 := by
        rw [Finset.sum_ite_eq' Finset.univ i]; simp
      rw [e, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      by_cases ha : a = i
      · subst ha
        simp
      · have hne : a.val ≠ i.val := fun h => ha (Fin.ext h)
        have hiff : a.val < i.succ.val ↔ a.val < i.castSucc.val := by
          simp only [Fin.val_succ, Fin.val_castSucc]; omega
        rw [if_neg ha, add_zero]
        simp only [hiff]
    rw [hsplit]
    by_cases hv : Lt.vec i = true
    · rw [if_pos hv] at hs
      rw [if_pos hv]
      obtain ⟨h1, -, h3⟩ := hs
      have h4 : P.mu i.succ 0 - P.mu i.castSucc 0 ≤ ∑ a, (P.mu i.succ a - P.mu i.castSucc a) :=
        Finset.single_le_sum (f := fun a => P.mu i.succ a - P.mu i.castSucc a)
          (fun a _ => sub_nonneg.2 (h1 a)) (Finset.mem_univ 0)
      rw [h3] at h4
      linarith
    · rw [if_neg hv] at hs
      rw [if_neg hv, add_zero]
      exact (hs.1 0).trans ih

theorem deg_even_le {s r : ℕ} (p : ℕ) (S : SegData s) (aTop : Fin s → ℕ) (aPlus : ℕ) (m : ℝ) (b : SegBlock s r)
    (lv : Fin (blockData p S aTop aPlus m b).T.t → ℕ) (jp : ℕ) (l : Fin s) (hl : (l : ℕ) < S.sigma) :
    ((blockData p S aTop aPlus m b).lettersAt lv jp).deg ⟨2 * l.val, by have := l.2; omega⟩ ≤ b.w l := by
  refine (Nat.sub_le _ _).trans ((Nat.sub_le _ _).trans ?_)
  show (segChain p S aTop b).deg ⟨2 * l.val, by have := l.2; omega⟩ ≤ b.w l
  have hne : ((⟨2 * l.val, by have := l.2; omega⟩ : Fin (2 * s + 1)) : ℕ) ≠ 2 * s := by
    have := l.2
    show 2 * l.val ≠ 2 * s
    omega
  have ht : topOf ⟨2 * l.val, by have := l.2; omega⟩ hne = l := Fin.ext (by show 2 * l.val / 2 = l.val; omega)
  unfold segChain
  simp only
  rw [dif_neg hne, if_pos (by omega), ht, if_pos hl]

theorem sum_deg_le {s r : ℕ} (p : ℕ) (S : SegData s) (aTop : Fin s → ℕ) (aPlus : ℕ) (m : ℝ) (b : SegBlock s r)
    (lv : Fin (blockData p S aTop aPlus m b).T.t → ℕ) (jp : ℕ) (l : Fin s) (hl : (l : ℕ) < S.sigma) :
    (∑ a : Fin (2 * s + 1), if a.val < 2 * l.val + 1 ∧
        ((blockData p S aTop aPlus m b).lettersAt lv jp).vec a = true then
        (((blockData p S aTop aPlus m b).lettersAt lv jp).deg a : ℤ) else 0) ≤
      ∑ l' : Fin s, (if (l' : ℕ) ≤ (l : ℕ) then (b.w l' : ℤ) else 0) := by
  have hvec : ∀ a, ((blockData p S aTop aPlus m b).lettersAt lv jp).vec a = decide ((a : ℕ) % 2 = 0) := fun _ => rfl
  rw [sum_fin_odd]
  have hlast : ¬ (2 * s < 2 * l.val + 1 ∧
      ((blockData p S aTop aPlus m b).lettersAt lv jp).vec ⟨2 * s, by omega⟩ = true) := by
    have := l.2
    intro h; omega
  rw [if_neg hlast, add_zero]
  refine Finset.sum_le_sum fun l' _ => ?_
  have hodd : ¬ (2 * l'.val + 1 < 2 * l.val + 1 ∧
      ((blockData p S aTop aPlus m b).lettersAt lv jp).vec ⟨2 * l'.val + 1, by have := l'.2; omega⟩ = true) := by
    rintro ⟨-, h⟩
    rw [hvec] at h
    simp only [decide_eq_true_eq] at h
    omega
  rw [if_neg hodd, add_zero]
  by_cases h : (l' : ℕ) ≤ (l : ℕ)
  · rw [if_pos h]
    split_ifs
    · exact_mod_cast deg_even_le p S aTop aPlus m b lv jp l' (by omega)
    · positivity
  · rw [if_neg h, if_neg (by rintro ⟨h1, -⟩; simp only at h1; omega)]

theorem bd_J_last {s r : ℕ} (p : ℕ) (S : SegData s) (aTop : Fin s → ℕ) (aPlus : ℕ) (m : ℝ) (b : SegBlock s r) :
    (blockData p S aTop aPlus m b).T.J (Fin.last S.t) = 2 * s + 1 :=
  dif_neg (lt_irrefl _)

theorem bd_thr_last {s r : ℕ} (p : ℕ) (S : SegData s) (aTop : Fin s → ℕ) (aPlus : ℕ) (m : ℝ) (b : SegBlock s r) :
    (blockData p S aTop aPlus m b).T.thr (Fin.last S.t) = ((⌊((cap p S b s : ℤ) : ℝ) - m⌋ : ℤ) : WithTop ℤ) := by
  show WithTop.map _ (segmentCapacities p S b (Fin.last S.t)) = _
  unfold segmentCapacities
  rw [dif_neg (show ¬ ((Fin.last S.t : Fin (S.t + 1)) : ℕ) < S.t from lt_irrefl _)]
  rfl

theorem bd_J_lt {s r : ℕ} (p : ℕ) (S : SegData s) (aTop : Fin s → ℕ) (aPlus : ℕ) (m : ℝ) (b : SegBlock s r)
    (q : ℕ) (h : q < S.t) :
    (blockData p S aTop aPlus m b).T.J (⟨q, Nat.lt_succ_of_lt h⟩ : Fin (S.t + 1)) = 2 * (S.sigma + q) + 1 :=
  dif_pos h

theorem bd_thr_lt {s r : ℕ} (p : ℕ) (S : SegData s) (aTop : Fin s → ℕ) (aPlus : ℕ) (m : ℝ) (b : SegBlock s r)
    (q : ℕ) (h : q < S.t) :
    (blockData p S aTop aPlus m b).T.thr (⟨q, Nat.lt_succ_of_lt h⟩ : Fin (S.t + 1)) =
      ((⌊((cap p S b (S.sigma + q) : ℤ) : ℝ) - m⌋ : ℤ) : WithTop ℤ) := by
  show WithTop.map _ (segmentCapacities p S b ⟨q, Nat.lt_succ_of_lt h⟩) = _
  unfold segmentCapacities
  rw [dif_pos h]
  rfl

theorem ph_seg {C0 Cde CE1 CE2 mu E : ℝ} {X : Loc} [NeZero X.m] {β : GlobalTheory X} (L : LvDat C0 CE1 CE2 mu X β)
    (j : Fin (numSeg X.TT)) (y : Tx X.m (L.LL j))
    (hy : y ∈ sAll (L.LL j) (BDk C0 CE1 CE2 mu X β j).T.J (BDk C0 CE1 CE2 mu X β j).T.thr)
    (hB : BLk C0 Cde CE1 CE2 X E j (β j))
    (hnum1 : (∑ l : Fin (segS X.TT j), (if (l : ℕ) < (X.seg C0 CE1 CE2 j).sigma then ((β j).sg l : ℤ) else 0)) ≤
      ⌊(((X.seg C0 CE1 CE2 j).A0 X.p : ℤ) : ℝ) - mu⌋)
    (hnum2 : ∀ i : Fin (segS X.TT j), (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma →
      (∑ l : Fin (segS X.TT j), (if (l : ℕ) ≤ (i : ℕ) then ((β j).w l : ℤ) else 0)) +
        (∑ l : Fin (segS X.TT j), (if (l : ℕ) < (X.seg C0 CE1 CE2 j).sigma then ((β j).sg l : ℤ) else 0)) ≤
        ⌊(((X.seg C0 CE1 CE2 j).A0 X.p : ℤ) : ℝ) - mu⌋)
    (hm : 2 * segS X.TT j + 1 < X.m) :
    Col.PH (L.LL j).vec (L.LL j).deg y.1.1.mu (nuS C0 CE1 CE2 mu X β j) := by
  have hvec : ∀ a, (L.LL j).vec a = decide ((a : ℕ) % 2 = 0) := fun _ => rfl
  have hw : ∀ l : Fin (segS X.TT j), (l : ℕ) < (X.seg C0 CE1 CE2 j).sigma →
      (β j).w l ≤ coarseA X.p (X.seg C0 CE1 CE2 j) (β j) l := fun l h => (hB.2.2.1 l h).2.1
  have ho : ∀ l : Fin (segS X.TT j), (X.seg C0 CE1 CE2 j).sigma ≤ (l : ℕ) →
      (β j).o l ≤ coarseA X.p (X.seg C0 CE1 CE2 j) (β j) l := fun l h => (hB.2.1 l h).1
  have ha0 : 0 ≤ a0Z C0 CE1 CE2 mu X β j := sub_nonneg.2 hnum1
  have hnu : ∀ T, T ≠ 0 → nuS C0 CE1 CE2 mu X β j T = a0Z C0 CE1 CE2 mu X β j +
      ∑ l : Fin (segS X.TT j), (if 2 * (l : ℕ) + 2 ≤ T then (zxS C0 CE1 CE2 X β j l : ℤ) else 0) := by
    intro T h
    unfold nuS
    rw [if_neg h]
  have hge : ∀ T, T ≠ 0 → a0Z C0 CE1 CE2 mu X β j ≤ nuS C0 CE1 CE2 mu X β j T := by
    intro T h
    rw [hnu T h]
    refine le_add_of_nonneg_right (Finset.sum_nonneg fun l _ => ?_)
    split_ifs
    · positivity
    · exact le_rfl
  have hfl : ∀ L0 : ℕ, (∀ l : Fin (segS X.TT j), (l : ℕ) < (X.seg C0 CE1 CE2 j).sigma → (l : ℕ) < L0) →
      ⌊((cap X.p (X.seg C0 CE1 CE2 j) (β j) L0 : ℤ) : ℝ) - mu⌋ = nuS C0 CE1 CE2 mu X β j (2 * L0 + 1) := by
    intro L0 hL
    rw [floor_cap X.p _ (β j) mu L0 hL hw ho, hnu _ (by omega)]
    rfl
  have h0 : nuS C0 CE1 CE2 mu X β j 0 = 0 := by
    unfold nuS
    rw [if_pos rfl]
  refine ⟨y.1.1.zero, y.1.1.dom, y.1.1.step, h0, ?_, ?_, ?_, hm⟩
  · intro t
    by_cases ht : t = 0
    · subst ht
      rw [h0]
      exact ha0.trans (hge _ (by omega))
    · rw [hnu t ht, hnu (t + 1) (by omega)]
      refine add_le_add_right (Finset.sum_le_sum fun l _ => ?_) _
      by_cases h : 2 * (l : ℕ) + 2 ≤ t
      · rw [if_pos h, if_pos (by omega)]
      · rw [if_neg h]
        split_ifs
        · positivity
        · exact le_rfl
  · intro i hi
    rw [hvec] at hi
    simp only [decide_eq_false_iff_not] at hi
    rw [hnu _ (by omega), hnu _ (by omega)]
    congr 1
    refine Finset.sum_congr rfl fun l _ => ?_
    exact if_congr (by omega) rfl rfl
  · intro i hi b
    rw [hvec] at hi
    simp only [decide_eq_true_eq] at hi
    refine (y.1.1.dom i.succ (Fin.zero_le b)).trans ?_
    have hi2 := i.2
    by_cases h1 : i.val = 2 * segS X.TT j
    · have hk := hy (Fin.last (X.seg C0 CE1 CE2 j).t)
      change ((y.1.1.mu (finPos _ ((BDk C0 CE1 CE2 mu X β j).T.J (Fin.last (X.seg C0 CE1 CE2 j).t))) 0 : ℤ) : WithTop ℤ) ≤
        (BDk C0 CE1 CE2 mu X β j).T.thr (Fin.last (X.seg C0 CE1 CE2 j).t) at hk
      rw [bd_J_last, bd_thr_last, WithTop.coe_le_coe, hfl _ (fun l _ => l.2)] at hk
      have e : finPos (2 * segS X.TT j + 1) (2 * segS X.TT j + 1) = i.succ :=
        Fin.ext (by simp only [finPos, Fin.val_succ]; omega)
      rw [e] at hk
      rw [h1]
      exact hk
    · obtain ⟨l, hl⟩ : ∃ l, i.val = 2 * l := ⟨i.val / 2, by omega⟩
      have hls : l < segS X.TT j := by omega
      by_cases h2 : l < (X.seg C0 CE1 CE2 j).sigma
      · have hf := first_row_le y.1.1 i.succ
        have e : (i.succ : Fin (2 * segS X.TT j + 1 + 1)).val = 2 * (⟨l, hls⟩ : Fin (segS X.TT j)).val + 1 := by
          simp only [Fin.val_succ]; omega
        rw [e] at hf
        have hs := sum_deg_le X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) mu (β j)
          (L.lv j) (L.jp j) ⟨l, hls⟩ h2
        have hn := hnum2 ⟨l, hls⟩ h2
        have hg := hge (i.val + 1) (by omega)
        have ha : (∑ l' : Fin (segS X.TT j), (if (l' : ℕ) ≤ ((⟨l, hls⟩ : Fin (segS X.TT j)) : ℕ) then ((β j).w l' : ℤ) else 0)) ≤
            a0Z C0 CE1 CE2 mu X β j := by
          unfold a0Z
          linarith
        exact hf.trans (hs.trans (ha.trans hg))
      · have hq : l - (X.seg C0 CE1 CE2 j).sigma < (X.seg C0 CE1 CE2 j).t := by
          unfold SegData.t; omega
        have hk := hy (⟨l - (X.seg C0 CE1 CE2 j).sigma, Nat.lt_succ_of_lt hq⟩ : Fin ((X.seg C0 CE1 CE2 j).t + 1))
        change ((y.1.1.mu (finPos _ ((BDk C0 CE1 CE2 mu X β j).T.J
          (⟨l - (X.seg C0 CE1 CE2 j).sigma, Nat.lt_succ_of_lt hq⟩ : Fin ((X.seg C0 CE1 CE2 j).t + 1)))) 0 : ℤ) : WithTop ℤ) ≤
          (BDk C0 CE1 CE2 mu X β j).T.thr
            (⟨l - (X.seg C0 CE1 CE2 j).sigma, Nat.lt_succ_of_lt hq⟩ : Fin ((X.seg C0 CE1 CE2 j).t + 1)) at hk
        rw [bd_J_lt _ _ _ _ _ _ _ hq, bd_thr_lt _ _ _ _ _ _ _ hq, WithTop.coe_le_coe] at hk
        have el : (X.seg C0 CE1 CE2 j).sigma + (l - (X.seg C0 CE1 CE2 j).sigma) = l := by omega
        rw [el, hfl l (fun l' h' => by omega)] at hk
        have e : finPos (2 * segS X.TT j + 1) (2 * l + 1) = i.succ :=
          Fin.ext (by simp only [finPos, Fin.val_succ]; omega)
        rw [e] at hk
        rw [hl]
        exact hk

end Formalism.MainNotions.ColumnSystems.Pf.GenusGluing
