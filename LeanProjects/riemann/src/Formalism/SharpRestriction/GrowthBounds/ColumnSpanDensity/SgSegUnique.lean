import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.MeanDefs
import Formalism.SharpRestriction.GrowthBounds.TopChoiceBounds

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.TopChoiceBounds

variable {n' : ℕ}

theorem sg_cdist (a b : Fin n') :
    cdist a b = if a.val ≤ b.val then b.val - a.val else b.val + n' - a.val := by
  have ha := a.isLt
  have hb := b.isLt
  unfold cdist
  split_ifs with h
  · rw [show b.val + n' - a.val = (b.val - a.val) + n' by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]
  · exact Nat.mod_eq_of_lt (by omega)

private lemma posAdd_cdist_eq_self (x y : Fin n') : posAdd x (cdist x y) = y := by
  have hx := x.isLt
  have hy := y.isLt
  apply Fin.ext
  show (x.val + (y.val + n' - x.val) % n') % n' = y.val
  rw [Nat.add_mod_mod, show x.val + (y.val + n' - x.val) = y.val + n' by omega, Nat.add_mod_right,
    Nat.mod_eq_of_lt hy]

theorem sg_pos_spec (TT : Finset (Fin n')) (j : Fin (numSeg TT)) (i : Fin (segS TT j)) :
    segPos TT j i ∈ TT ∧ ¬ Even (segPos TT j i).val ∧
      cdist (segStart TT j) (segPos TT j i) = (segDists TT j).get i ∧
      0 < cdist (segStart TT j) (segPos TT j i) ∧ cdist (segStart TT j) (segPos TT j i) < segG TT j := by
  obtain ⟨s, hs, hsd⟩ := Finset.mem_image.1 ((Finset.mem_sort _).1 (List.get_mem (segDists TT j) i))
  obtain ⟨hsT, hodd, hpos, hlt⟩ := Finset.mem_filter.1 hs
  have hp : segPos TT j i = s := by
    unfold segPos
    rw [← hsd]
    exact posAdd_cdist_eq_self _ _
  rw [hp]
  exact ⟨hsT, hodd, hsd, hpos, hlt⟩

theorem sg_next_mem (TT : Finset (Fin n')) (j : Fin (numSeg TT)) :
    segNext TT j ∈ TT ∧ Even (segNext TT j).val :=
  (bs_mem TT (segNext TT j)).1 (List.get_mem _ _)

theorem sg_dists_inj (TT : Finset (Fin n')) (j : Fin (numSeg TT)) : Function.Injective (segDists TT j).get :=
  List.nodup_iff_injective_get.1 (by unfold segDists; apply Finset.sort_nodup)

theorem sg_pos_inj (TT : Finset (Fin n')) (j : Fin (numSeg TT)) : Function.Injective (segPos TT j) := by
  intro i i' h
  have e1 := (sg_pos_spec TT j i).2.2.1
  have e2 := (sg_pos_spec TT j i').2.2.1
  rw [h] at e1
  exact sg_dists_inj TT j (e1.symm.trans e2)

def sgTop (TT : Finset (Fin n')) (j : Fin (numSeg TT)) : Option (Fin (segS TT j)) → TT
  | none => ⟨segNext TT j, (sg_next_mem TT j).1⟩
  | some i => ⟨segPos TT j i, (sg_pos_spec TT j i).1⟩

theorem sgTop_inj (TT : Finset (Fin n')) (j : Fin (numSeg TT)) : Function.Injective (sgTop TT j) := by
  rintro (_ | i) (_ | i') h
  · rfl
  · exfalso
    have h' : segNext TT j = segPos TT j i' := congrArg Subtype.val h
    have e := (sg_next_mem TT j).2
    rw [h'] at e
    exact (sg_pos_spec TT j i').2.1 e
  · exfalso
    have h' : segPos TT j i = segNext TT j := congrArg Subtype.val h
    have e := (sg_next_mem TT j).2
    rw [← h'] at e
    exact (sg_pos_spec TT j i).2.1 e
  · exact congrArg some (sg_pos_inj TT j (congrArg Subtype.val h))

def sgAll (TT : Finset (Fin n')) : (Σ j : Fin (numSeg TT), Option (Fin (segS TT j))) → TT
  | ⟨j, none⟩ => ⟨segStart TT j, (bs_start_mem TT j).1⟩
  | ⟨j, some i⟩ => ⟨segPos TT j i, (sg_pos_spec TT j i).1⟩

theorem sg_seg_unique (TT : Finset (Fin n')) (h2 : 2 ≤ numSeg TT) (j j' : Fin (numSeg TT)) (i : Fin (segS TT j))
    (i' : Fin (segS TT j')) (h : segPos TT j i = segPos TT j' i') : j = j' := by
  by_contra hne
  have hs : segStart TT j ≠ segStart TT j' := fun e => hne ((bs_mono TT).injective e)
  have m1 := bs_min TT h2 j (segStart TT j') (bs_start_mem TT j').1 (bs_start_mem TT j').2 hs.symm
  have m2 := bs_min TT h2 j' (segStart TT j) (bs_start_mem TT j).1 (bs_start_mem TT j).2 hs
  have hG1 : segG TT j = cdist (segStart TT j) (segNext TT j) := by
    unfold segG
    rw [if_neg (by omega)]
  have hG2 : segG TT j' = cdist (segStart TT j') (segNext TT j') := by
    unfold segG
    rw [if_neg (by omega)]
  have A := (sg_pos_spec TT j i).2.2.2.2
  have B := (sg_pos_spec TT j' i').2.2.2.2
  rw [h, hG1] at A
  rw [hG2] at B
  have X1 := lt_of_lt_of_le A m1.2
  have X2 := lt_of_lt_of_le B m2.2
  have ha := (segStart TT j).isLt
  have hb := (segStart TT j').isLt
  have hp := (segPos TT j' i').isLt
  rw [sg_cdist, sg_cdist] at X1 X2
  split_ifs at X1 X2 <;> omega

theorem sgAll_inj (TT : Finset (Fin n')) (h2 : 2 ≤ numSeg TT) : Function.Injective (sgAll TT) := by
  rintro ⟨j, _ | i⟩ ⟨j', _ | i'⟩ h
  · have h' : segStart TT j = segStart TT j' := congrArg Subtype.val h
    obtain rfl := (bs_mono TT).injective h'
    rfl
  · exfalso
    have h' : segStart TT j = segPos TT j' i' := congrArg Subtype.val h
    have e := (bs_start_mem TT j).2
    rw [h'] at e
    exact (sg_pos_spec TT j' i').2.1 e
  · exfalso
    have h' : segPos TT j i = segStart TT j' := congrArg Subtype.val h
    have e := (bs_start_mem TT j').2
    rw [← h'] at e
    exact (sg_pos_spec TT j i).2.1 e
  · have h' : segPos TT j i = segPos TT j' i' := congrArg Subtype.val h
    obtain rfl := sg_seg_unique TT h2 j j' i i' h'
    rw [sg_pos_inj TT j h']

theorem sg_count (TT : Finset (Fin n')) (h2 : 2 ≤ numSeg TT) :
    ∑ j : Fin (numSeg TT), (segS TT j + 1) ≤ TT.card := by
  have hc := Fintype.card_le_of_injective _ (sgAll_inj TT h2)
  simpa [Fintype.card_sigma] using hc

end Formalism.MainNotions.flipOneThree.Pf

end
