import Mathlib
import Formalism.PeriodIntegrals.SupportParts

noncomputable section

namespace PI.SupportDatumW

open NumberField IsDedekindDomain Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups ValuativeRel
open scoped BigOperators ComplexOrder
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def blkDet {K : Type} [CommRing K] : List (K × ℕ) → K
  | [] => 1
  | (t, s) :: bs => (-1) ^ (s * (s - 1) / 2) * t ^ s * blkDet bs

theorem antidiag_det {K : Type} [CommRing K] (t : K) (s : ℕ) :
    (Matrix.of fun a b : Fin s => if a.val + b.val + 1 = s then t else 0).det =
      (-1) ^ (s * (s - 1) / 2) * t ^ s := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [Matrix.det_succ_row_zero, Finset.sum_eq_single (Fin.last s)]
    · have hm : ((Matrix.of fun a b : Fin (s + 1) => if a.val + b.val + 1 = s + 1 then t else 0).submatrix
          Fin.succ (Fin.last s).succAbove) =
          Matrix.of fun a b : Fin s => if a.val + b.val + 1 = s then t else 0 := by
        ext a b
        simp only [Matrix.submatrix_apply, Matrix.of_apply, Fin.succAbove_last, Fin.val_succ,
          Fin.coe_castSucc]
        split_ifs <;> first | rfl | omega
      rw [hm, ih]
      simp only [Matrix.of_apply, Fin.val_zero, Fin.val_last, zero_add, eq_self_iff_true, if_true]
      have hexp : (s + 1) * (s + 1 - 1) / 2 = s + s * (s - 1) / 2 := by
        rcases s with _ | k
        · rfl
        · have hk : (k + 1 + 1) * (k + 1 + 1 - 1) = (k + 1) * (k + 1 - 1) + 2 * (k + 1) := by
            simp only [Nat.add_sub_cancel]
            ring
          rw [hk, Nat.add_mul_div_left _ _ (by norm_num : 0 < 2)]
          exact Nat.add_comm _ _
      rw [hexp]
      ring
    · intro j _ hj
      have hj' : (j : ℕ) ≠ s := fun h => hj (Fin.ext (by rw [Fin.val_last]; exact h))
      simp [hj']
    · intro h
      exact absurd (Finset.mem_univ _) h

theorem ptEntry_det {K : Type} [CommRing K] (bs : List (K × ℕ)) (n : ℕ)
    (h : (bs.map Prod.snd).sum = n) :
    (Matrix.of fun a b : Fin n => ptEntry bs a.val b.val).det = blkDet bs := by
  induction bs generalizing n with
  | nil =>
    simp at h
    subst h
    simp [blkDet]
  | cons x bs ih =>
    obtain ⟨t, s⟩ := x
    simp only [List.map_cons, List.sum_cons] at h
    subst h
    rw [← Matrix.det_submatrix_equiv_self finSumFinEquiv]
    have hb : (Matrix.of fun a b : Fin (s + (bs.map Prod.snd).sum) =>
        ptEntry ((t, s) :: bs) a.val b.val).submatrix finSumFinEquiv finSumFinEquiv =
        Matrix.fromBlocks (Matrix.of fun a b : Fin s => if a.val + b.val + 1 = s then t else 0) 0 0
          (Matrix.of fun a b : Fin (bs.map Prod.snd).sum => ptEntry bs a.val b.val) := by
      ext (a | a) (b | b)
      all_goals
        have ha := a.2
        have hb' := b.2
        simp only [Matrix.submatrix_apply, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
          Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
          Matrix.fromBlocks_apply₂₂, Matrix.of_apply, Fin.coe_castAdd, Fin.coe_natAdd,
          Matrix.zero_apply, ptEntry]
        split_ifs <;> first | rfl | omega | simp
    rw [hb, Matrix.det_fromBlocks_zero₂₁, antidiag_det, ih _ rfl]
    simp [blkDet]

theorem ptEntryL_eq {E : Type} [CommRing E] (l : List (Eˣ × ℕ+)) (a b : ℕ) :
    Loc.ptEntryL l a b = ptEntry (l.map fun x => ((x.1 : E), (x.2 : ℕ))) a b := by
  induction l generalizing a b with
  | nil => simp [Loc.ptEntryL, ptEntry]
  | cons x l ih =>
    obtain ⟨t, s⟩ := x
    simp only [Loc.ptEntryL, List.map_cons, ptEntry, ih]

theorem ptEntry_append_lt {K : Type} [Zero K] (head tail : List (K × ℕ)) (a b : ℕ)
    (ha : a < (head.map Prod.snd).sum) (hb : b < (head.map Prod.snd).sum) :
    ptEntry (head ++ tail) a b = ptEntry head a b := by
  induction head generalizing a b with
  | nil => simp at ha
  | cons x hd ih =>
    obtain ⟨t, s⟩ := x
    simp only [List.map_cons, List.sum_cons] at ha hb
    simp only [List.cons_append, ptEntry]
    split_ifs <;> first | rfl | exact ih _ _ (by omega) (by omega)

theorem ptEntry_append_ge {K : Type} [Zero K] (head tail : List (K × ℕ)) (a b : ℕ)
    (ha : (head.map Prod.snd).sum ≤ a) :
    ptEntry (head ++ tail) a b =
      if (head.map Prod.snd).sum ≤ b then
        ptEntry tail (a - (head.map Prod.snd).sum) (b - (head.map Prod.snd).sum) else 0 := by
  induction head generalizing a b with
  | nil => simp
  | cons x hd ih =>
    obtain ⟨t, s⟩ := x
    simp only [List.map_cons, List.sum_cons] at ha ⊢
    simp only [List.cons_append, ptEntry]
    have hna : ¬ (a < s ∧ b < s) := by omega
    rw [if_neg hna]
    by_cases hb : s ≤ b
    · rw [if_pos ⟨by omega, hb⟩, ih (a - s) (b - s) (by omega)]
      by_cases hc : (hd.map Prod.snd).sum ≤ b - s
      · rw [if_pos hc, if_pos (by omega), Nat.sub_sub, Nat.sub_sub]
      · rw [if_neg hc, if_neg (by omega)]
    · rw [if_neg (by omega), if_neg (by omega)]

theorem blkDet_ne_zero {K : Type} [CommRing K] [IsDomain K] (bs : List (K × ℕ))
    (h : ∀ b ∈ bs, b.1 ≠ 0) : blkDet bs ≠ 0 := by
  induction bs with
  | nil => simp [blkDet]
  | cons b bs ih =>
    obtain ⟨t, s⟩ := b
    have ht : t ≠ 0 := h (t, s) (by simp)
    have hbs : blkDet bs ≠ 0 := ih (fun b hb => h b (by simp [hb]))
    simp only [blkDet]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) (pow_ne_zero _ ht)) hbs

theorem dmin_top (D : Formalism.BasicNotions.D7) {n : ℕ} (w : Point D.host.E n) : Dmin w n = blkDet w.1 := by
  have hw := w.2
  unfold Dmin ptMat
  rw [dif_pos le_rfl, ← ptEntry_det w.1 n hw.2]
  congr 1

theorem topNe (D : Formalism.BasicNotions.D7) (w : Point D.host.E (D.R.rS + 1)) : Dmin w (D.R.rS + 1) ≠ 0 := by
  rw [dmin_top]
  exact blkDet_ne_zero _ (fun b hb => (w.2.1 b hb).1)

theorem dmin_last_one (D : Formalism.BasicNotions.D7) (w : Point D.host.E (D.R.rS + 1))
    (head : List (D.host.E × ℕ)) (t : D.host.E) (h : w.1 = head ++ [(t, 1)]) :
    Dmin w D.R.rS = blkDet head := by
  have h2 := w.2.2
  rw [h] at h2
  simp at h2
  have hsum : (head.map Prod.snd).sum = D.R.rS := by omega
  unfold Dmin ptMat
  rw [dif_pos (Nat.le_succ _), ← ptEntry_det head D.R.rS hsum]
  congr 1
  ext a b
  change ptEntry w.1 a.val b.val = ptEntry head a.val b.val
  rw [h, ptEntry_append_lt head _ _ _ (by rw [hsum]; exact a.2) (by rw [hsum]; exact b.2)]

theorem dmin_last_big (D : Formalism.BasicNotions.D7) (w : Point D.host.E (D.R.rS + 1))
    (head : List (D.host.E × ℕ)) (t : D.host.E) (s : ℕ)
    (h : w.1 = head ++ [(t, s)]) (hs : 2 ≤ s) : Dmin w D.R.rS = 0 := by
  have h2 := w.2.2
  rw [h] at h2
  simp at h2
  unfold Dmin ptMat
  rw [dif_pos (Nat.le_succ _)]
  apply Matrix.det_eq_zero_of_row_eq_zero ⟨(head.map Prod.snd).sum, by omega⟩
  intro b
  have hb2 := b.2
  change ptEntry w.1 (head.map Prod.snd).sum b.val = 0
  rw [h, ptEntry_append_ge head _ _ _ le_rfl]
  split_ifs with hb
  · simp only [ptEntry]
    split_ifs <;> first | rfl | omega
  · rfl

end PI.SupportDatumW
