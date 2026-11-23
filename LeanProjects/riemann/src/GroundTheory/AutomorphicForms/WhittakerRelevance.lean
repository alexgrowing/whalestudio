import Mathlib

namespace GroundTheory.Automorphic

namespace Whittaker

open Finset

variable {n : ℕ} {w : Equiv.Perm (Fin n)}

theorem val_eq_of_le_of_le
    (hB : ∀ i j : Fin n, i < j → (w j).val = (w i).val + 1 → j.val = i.val + 1) :
    ∀ (g : ℕ) (z y : Fin n), (w y).val = (w z).val + g → z ≤ y →
      ∀ x : Fin n, z ≤ x → x ≤ y → (w x).val = (w z).val + (x.val - z.val) := by
  intro g
  induction g using Nat.strong_induction_on with
  | _ g ih =>
  intro z y hgap hzy x hzx hxy
  rw [Fin.le_iff_val_le_val] at hzy hzx hxy
  rcases Nat.eq_zero_or_pos g with hg | hg
  · subst hg
    have hyz : y = z := w.injective (Fin.ext (by omega))
    subst hyz
    have hxy' : x = y := Fin.ext (by omega)
    subst hxy'
    simp
  · have hlt : (w z).val + 1 < n := by have := (w y).isLt; omega
    set p := w.symm ⟨(w z).val + 1, hlt⟩ with hp
    have hwp : (w p).val = (w z).val + 1 := by simp [hp]
    have hzy' : z.val < y.val := by
      rcases Nat.lt_or_eq_of_le hzy with h | h
      · exact h
      · have : z = y := Fin.ext h
        subst this
        omega
    rcases lt_trichotomy p.val z.val with hpz | hpz | hpz
    ·
      exfalso
      have key := ih (g - 1) (by omega) p y (by omega) (Fin.le_iff_val_le_val.2 (by omega)) z
        (Fin.le_iff_val_le_val.2 (by omega)) (Fin.le_iff_val_le_val.2 hzy)
      omega
    · exfalso
      have : p = z := Fin.ext hpz
      rw [this] at hwp
      omega
    ·
      have hp1 : p.val = z.val + 1 := hB z p (Fin.lt_def.2 hpz) hwp
      rcases Nat.eq_or_lt_of_le hzx with hx | hx
      · have : x = z := Fin.ext hx.symm
        subst this
        simp
      · have key := ih (g - 1) (by omega) p y (by omega) (Fin.le_iff_val_le_val.2 (by omega)) x
          (Fin.le_iff_val_le_val.2 (by omega)) (Fin.le_iff_val_le_val.2 hxy)
        omega

theorem val_eq_of_le_right
    (hB : ∀ i j : Fin n, i < j → (w j).val = (w i).val + 1 → j.val = i.val + 1) (b x : Fin n)
    (hbx : b ≤ x) (hx : x.val ≤ b.val + #(univ.filter fun y : Fin n => b < y ∧ w b < w y)) :
    (w x).val = (w b).val + (x.val - b.val) := by
  set R := univ.filter fun y : Fin n => b < y ∧ w b < w y with hR
  by_cases hne : R.Nonempty
  · set m := R.max' hne
    have hm : m ∈ R := R.max'_mem hne
    rw [hR, mem_filter] at hm
    have hsub : R ⊆ Ioc b m := by
      intro y hy
      have hy' := hy
      rw [hR, mem_filter] at hy'
      exact mem_Ioc.2 ⟨hy'.2.1, R.le_max' y hy⟩
    have hcard : #R ≤ m.val - b.val := by
      have := card_le_card hsub
      rwa [Fin.card_Ioc] at this
    have hbm := Fin.lt_def.1 hm.2.1
    have hwbm := Fin.lt_def.1 hm.2.2
    exact val_eq_of_le_of_le hB ((w m).val - (w b).val) b m (by omega) (le_of_lt hm.2.1) x hbx
      (Fin.le_iff_val_le_val.2 (by omega))
  · rw [not_nonempty_iff_eq_empty] at hne
    rw [hne, card_empty] at hx
    have : x = b := Fin.ext (by rw [Fin.le_iff_val_le_val] at hbx; omega)
    subst this
    simp

theorem val_add_eq_of_le_left
    (hB : ∀ i j : Fin n, i < j → (w j).val = (w i).val + 1 → j.val = i.val + 1) (b x : Fin n)
    (hxb : x ≤ b) (hx : b.val ≤ x.val + #(univ.filter fun y : Fin n => y < b ∧ w y < w b)) :
    (w x).val + (b.val - x.val) = (w b).val := by
  set L := univ.filter fun y : Fin n => y < b ∧ w y < w b with hL
  by_cases hne : L.Nonempty
  · set m := L.min' hne
    have hm : m ∈ L := L.min'_mem hne
    rw [hL, mem_filter] at hm
    have hsub : L ⊆ Ico m b := by
      intro y hy
      have hy' := hy
      rw [hL, mem_filter] at hy'
      exact mem_Ico.2 ⟨L.min'_le y hy, hy'.2.1⟩
    have hcard : #L ≤ b.val - m.val := by
      have := card_le_card hsub
      rwa [Fin.card_Ico] at this
    have hmb := Fin.lt_def.1 hm.2.1
    have hwmb := Fin.lt_def.1 hm.2.2
    have h1 := val_eq_of_le_of_le hB ((w b).val - (w m).val) m b (by omega) (le_of_lt hm.2.1) x
      (Fin.le_iff_val_le_val.2 (by omega)) hxb
    have h2 := val_eq_of_le_of_le hB ((w b).val - (w m).val) m b (by omega) (le_of_lt hm.2.1) b
      (le_of_lt hm.2.1) le_rfl
    rw [Fin.le_iff_val_le_val] at hxb
    omega
  · rw [not_nonempty_iff_eq_empty] at hne
    rw [hne, card_empty] at hx
    have : x = b := Fin.ext (by rw [Fin.le_iff_val_le_val] at hxb; omega)
    subst this
    simp

theorem card_filter_lt_apply (w : Equiv.Perm (Fin n)) (b : Fin n) :
    #(univ.filter fun x : Fin n => w x < w b) = (w b).val := by
  have : (univ.filter fun x : Fin n => w x < w b) = (Iio (w b)).map w.symm.toEmbedding := by
    ext x
    simp [mem_map_equiv]
  rw [this, card_map, Fin.card_Iio]

theorem val_add_card_right (w : Equiv.Perm (Fin n)) (b : Fin n) :
    (w b).val + #(univ.filter fun y : Fin n => b < y ∧ w b < w y) =
      #(univ.filter fun y : Fin n => y < b ∧ w y < w b) + (n - 1 - b.val) := by
  have hIoi : #(univ.filter fun y : Fin n => b < y) = n - 1 - b.val := by
    have : (univ.filter fun y : Fin n => b < y) = Ioi b := by
      ext y
      simp
    rw [this, Fin.card_Ioi]
  rw [← card_filter_lt_apply w b, ← hIoi, card_filter, card_filter, card_filter, card_filter,
    ← sum_add_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun y _ => ?_
  have hne : y ≠ b → w y ≠ w b := fun h e => h (w.injective e)
  rcases lt_trichotomy y b with h | h | h
  · have h' : ¬ b < y := not_lt.2 (le_of_lt h)
    by_cases hw : w y < w b <;> simp [h, h', hw]
  · subst h
    simp
  · have h' : ¬ y < b := not_lt.2 (le_of_lt h)
    have hyb : w y ≠ w b := hne (ne_of_gt h)
    rcases lt_or_gt_of_ne hyb with hw | hw
    · have hw' : ¬ w b < w y := not_lt.2 (le_of_lt hw)
      simp [h, h', hw, hw']
    · have hw' : ¬ w y < w b := not_lt.2 (le_of_lt hw)
      simp [h, h', hw, hw']

theorem relevant_involution
    (hB : ∀ i j : Fin n, i < j → (w j).val = (w i).val + 1 → j.val = i.val + 1) (b : Fin n) :
    w (Fin.rev (w b)) = Fin.rev b := by
  have hid := val_add_card_right w b
  set r := #(univ.filter fun y : Fin n => b < y ∧ w b < w y)
  set l := #(univ.filter fun y : Fin n => y < b ∧ w y < w b)
  set c := Fin.rev (w b) with hc
  have hcv : c.val = n - (↑(w b) + 1) := by rw [hc, Fin.val_rev]
  have hb := b.isLt
  have hwb := (w b).isLt
  apply Fin.ext
  rw [Fin.val_rev]
  by_cases hcb : b.val ≤ c.val
  · have := val_eq_of_le_right hB b c (Fin.le_iff_val_le_val.2 hcb) (by omega)
    omega
  · have := val_add_eq_of_le_left hB b c (Fin.le_iff_val_le_val.2 (by omega)) (by omega)
    omega

theorem apply_eq_of_run_right {α : Type*} (t : Fin n → α)
    (hB : ∀ i j : Fin n, i < j → (w j).val = (w i).val + 1 → j.val = i.val + 1)
    (ht : ∀ (i : Fin n) (h : i.val + 1 < n), w i < w ⟨i.val + 1, h⟩ →
      t (w i) = t (w ⟨i.val + 1, h⟩))
    (b : Fin n) :
    ∀ k : ℕ, ∀ x : Fin n, x.val = b.val + k →
      k ≤ #(univ.filter fun y : Fin n => b < y ∧ w b < w y) → t (w x) = t (w b) := by
  intro k
  induction k with
  | zero =>
    intro x hx _
    have : x = b := Fin.ext (by omega)
    rw [this]
  | succ k ih =>
    intro x hx hk
    have hxn := x.isLt
    have hk1 : b.val + k < n := by omega
    have h1 := ih ⟨b.val + k, hk1⟩ rfl (by omega)
    have e1 := val_eq_of_le_right hB b x (Fin.le_iff_val_le_val.2 (by omega)) (by omega)
    have e2 := val_eq_of_le_right hB b ⟨b.val + k, hk1⟩ (Fin.le_iff_val_le_val.2 (by simp))
      (by simp; omega)
    have hk2 : b.val + k + 1 < n := by omega
    have hnext : (⟨b.val + k + 1, hk2⟩ : Fin n) = x := Fin.ext (by simp; omega)
    have hasc : w ⟨b.val + k, hk1⟩ < w ⟨b.val + k + 1, hk2⟩ := by
      rw [hnext, Fin.lt_def]
      simp only at e2
      omega
    have := ht ⟨b.val + k, hk1⟩ hk2 hasc
    simp only at this
    rw [hnext] at this
    rw [← this, h1]

theorem apply_eq_of_run_left {α : Type*} (t : Fin n → α)
    (hB : ∀ i j : Fin n, i < j → (w j).val = (w i).val + 1 → j.val = i.val + 1)
    (ht : ∀ (i : Fin n) (h : i.val + 1 < n), w i < w ⟨i.val + 1, h⟩ →
      t (w i) = t (w ⟨i.val + 1, h⟩))
    (b : Fin n) :
    ∀ k : ℕ, ∀ x : Fin n, x.val + k = b.val →
      k ≤ #(univ.filter fun y : Fin n => y < b ∧ w y < w b) → t (w x) = t (w b) := by
  intro k
  induction k with
  | zero =>
    intro x hx _
    have : x = b := Fin.ext (by omega)
    rw [this]
  | succ k ih =>
    intro x hx hk
    have hbn := b.isLt
    have hx1 : x.val + 1 < n := by omega
    have h1 := ih ⟨x.val + 1, hx1⟩ (by simp; omega) (by omega)
    have e1 := val_add_eq_of_le_left hB b x (Fin.le_iff_val_le_val.2 (by omega)) (by omega)
    have e2 := val_add_eq_of_le_left hB b ⟨x.val + 1, hx1⟩ (Fin.le_iff_val_le_val.2 (by simp; omega))
      (by simp; omega)
    have hasc : w x < w ⟨x.val + 1, hx1⟩ := by
      rw [Fin.lt_def]
      simp only at e2
      omega
    have := ht x hx1 hasc
    rw [this]
    exact h1

theorem relevant_torus {α : Type*} (t : Fin n → α)
    (hB : ∀ i j : Fin n, i < j → (w j).val = (w i).val + 1 → j.val = i.val + 1)
    (ht : ∀ (i : Fin n) (h : i.val + 1 < n), w i < w ⟨i.val + 1, h⟩ →
      t (w i) = t (w ⟨i.val + 1, h⟩))
    (b : Fin n) : t (w b) = t (Fin.rev b) := by
  have hid := val_add_card_right w b
  rw [← relevant_involution hB b]
  set c := Fin.rev (w b) with hc
  have hcv : c.val = n - (↑(w b) + 1) := by rw [hc, Fin.val_rev]
  have hb := b.isLt
  have hwb := (w b).isLt
  by_cases hcb : b.val ≤ c.val
  · exact (apply_eq_of_run_right t hB ht b (c.val - b.val) c (by omega) (by omega)).symm
  · exact (apply_eq_of_run_left t hB ht b (b.val - c.val) c (by omega) (by omega)).symm

end Whittaker

end GroundTheory.Automorphic
