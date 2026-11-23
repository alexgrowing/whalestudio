import Mathlib
import Formalism.PeriodIntegrals.LongWeylElementSquare

noncomputable section

open Matrix

namespace PI.SwBig.GU

variable {k r : ℕ}

macro "lvo" : tactic => `(tactic| (intro a b c h1 h2; (try dsimp only at h1 h2 ⊢); omega))

def lv (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℕ :=
  if i.val < r then i.val else if i.val ≤ r + k then r else i.val - k

def sg (k r : ℕ) (i : Fin (2 * r + k + 1)) : Fin (2 * r + k + 1) :=
  ⟨if r ≤ i.val ∧ i.val ≤ r + k then i.val else 2 * r + k - i.val, by
    have := i.isLt; split_ifs <;> omega⟩

def sn (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℂ := if i.val = r + k then -1 else 1

def M (k r : ℕ) (f : Fin (2 * r + k + 1) → ℂ) : Mat k r := fun x z => if x = sg k r z then f z else 0

theorem sg_val (i : Fin (2 * r + k + 1)) :
    (sg k r i).val = if r ≤ i.val ∧ i.val ≤ r + k then i.val else 2 * r + k - i.val := rfl

theorem sg_sg (i : Fin (2 * r + k + 1)) : sg k r (sg k r i) = i := by
  apply Fin.ext; have := i.isLt; rw [sg_val, sg_val]; split_ifs <;> omega

theorem sg_inj {i j : Fin (2 * r + k + 1)} (h : sg k r i = sg k r j) : i = j := by
  rw [← sg_sg i, h, sg_sg]

theorem lv_sg (i : Fin (2 * r + k + 1)) : lv k r (sg k r i) = 2 * r - lv k r i := by
  have := i.isLt; unfold lv; rw [sg_val]; split_ifs <;> omega

theorem lv_le (i : Fin (2 * r + k + 1)) : lv k r i ≤ 2 * r := by
  have := i.isLt; unfold lv; split_ifs <;> omega

theorem sn_sg (i : Fin (2 * r + k + 1)) : sn k r (sg k r i) = sn k r i := by
  have := i.isLt; unfold sn; rw [sg_val]; split_ifs <;> first | rfl | (exfalso; omega)

theorem sn_mul_self (i : Fin (2 * r + k + 1)) : sn k r i * sn k r i = 1 := by
  unfold sn; split_ifs <;> norm_num

theorem sn_ne_zero (i : Fin (2 * r + k + 1)) : sn k r i ≠ 0 := by
  unfold sn; split_ifs <;> norm_num

theorem M_mul_apply (f : Fin (2 * r + k + 1) → ℂ) (A : Mat k r) (x y : Fin (2 * r + k + 1)) :
    (M k r f * A) x y = f (sg k r x) * A (sg k r x) y := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (sg k r x)]
  · simp [M, sg_sg]
  · intro z _ hz
    have : x ≠ sg k r z := by rintro rfl; exact hz (sg_sg z).symm
    simp [M, this]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem mul_M_apply (A : Mat k r) (g : Fin (2 * r + k + 1) → ℂ) (x y : Fin (2 * r + k + 1)) :
    (A * M k r g) x y = A x (sg k r y) * g y := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (sg k r y)]
  · simp [M]
  · intro z _ hz; simp [M, hz]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem M_mul (f g : Fin (2 * r + k + 1) → ℂ) :
    M k r f * M k r g = diagonal (fun y => f (sg k r y) * g y) := by
  ext x y
  rw [mul_M_apply, diagonal_apply]
  simp only [M]
  by_cases h : x = y
  · subst h; simp [sg_sg]
  · have : x ≠ sg k r (sg k r y) := by rw [sg_sg]; exact h
    simp [h, this]

theorem Hpk_eq : Hpk k r = M k r (sn k r) := by
  ext x z
  have := x.isLt; have := z.isLt
  simp only [Hpk, M, Fin.ext_iff, sg_val, sn]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem bigCell_eq (c : Fin r → ℂ) : bigCell k r c 1 = M k r (tv k r c) := by
  ext x z
  have := x.isLt; have := z.isLt
  unfold bigCell M tv
  simp only [esI, Fin.ext_iff, sg_val, Matrix.one_apply]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem Hpk_sq : Hpk k r * Hpk k r = 1 := by
  rw [Hpk_eq, M_mul, ← diagonal_one]; congr 1; funext y; rw [sn_sg, sn_mul_self]

theorem tv_ne_zero {c : Fin r → ℂ} (hc : ∀ a, c a ≠ 0) (i : Fin (2 * r + k + 1)) : tv k r c i ≠ 0 := by
  unfold tv; split_ifs
  · exact hc _
  · exact one_ne_zero
  · exact inv_ne_zero (star_ne_zero.mpr (hc _))

theorem bigCell_inv {c : Fin r → ℂ} (hc : ∀ a, c a ≠ 0) :
    (bigCell k r c 1)⁻¹ = M k r (fun y => (tv k r c (sg k r y))⁻¹) ∧
    (bigCell k r c 1)⁻¹ * bigCell k r c 1 = 1 := by
  have h1 : bigCell k r c 1 * M k r (fun y => (tv k r c (sg k r y))⁻¹) = 1 := by
    rw [bigCell_eq, M_mul, ← diagonal_one]; congr 1; funext y
    exact mul_inv_cancel₀ (tv_ne_zero hc _)
  have h2 := Matrix.inv_eq_right_inv h1
  refine ⟨h2, ?_⟩
  rw [h2]; exact mul_eq_one_comm.mp h1

theorem inv_of_UH {g : Mat k r} (hg : g ∈ UH (Hpk k r)) :
    g⁻¹ = Hpk k r * gᴴ * Hpk k r ∧ g⁻¹ * g = 1 ∧ g * g⁻¹ = 1 := by
  have hU : gᴴ * Hpk k r * g = Hpk k r := hg
  have h1 : Hpk k r * gᴴ * Hpk k r * g = 1 := by
    calc Hpk k r * gᴴ * Hpk k r * g = Hpk k r * (gᴴ * Hpk k r * g) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hU, Hpk_sq]
  have hinv := Matrix.inv_eq_left_inv h1
  refine ⟨hinv, ?_, ?_⟩
  · rw [hinv]; exact h1
  · rw [hinv]; exact mul_eq_one_comm.mp h1

theorem cL {A B X : Mat k r} (h : A * B = 1) : A * (B * X) = X := by
  rw [← Matrix.mul_assoc, h, Matrix.one_mul]

def Supp (A : Mat k r) (R : ℕ → ℕ → Prop) : Prop := ∀ x y, A x y ≠ 0 → R (lv k r x) (lv k r y)

theorem Supp.mul' {A B : Mat k r} {R S T : ℕ → ℕ → Prop} (hA : Supp A R) (hB : Supp B S)
    (hT : ∀ a b c, R a b → S b c → T a c) : Supp (A * B) T := by
  intro x y h
  rw [Matrix.mul_apply] at h
  obtain ⟨z, _, hz⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  exact hT _ _ _ (hA x z (left_ne_zero_of_mul hz)) (hB z y (right_ne_zero_of_mul hz))

theorem Supp.conjT {A : Mat k r} {R : ℕ → ℕ → Prop} (h : Supp A R) : Supp Aᴴ (fun a b => R b a) := by
  intro x y hxy
  exact h y x (fun h0 => hxy (by rw [conjTranspose_apply, h0, star_zero]))

theorem supp_M (f : Fin (2 * r + k + 1) → ℂ) : Supp (M k r f) (fun a b => a + b = 2 * r) := by
  intro x y h
  simp only [M] at h
  split_ifs at h with hx
  · subst hx; have := lv_sg (k := k) (r := r) y; have := lv_le (k := k) (r := r) y; omega
  · exact absurd rfl h

def NU (A : Mat k r) : Prop := ∀ x y, lv k r y ≤ lv k r x → A x y = (1 : Mat k r) x y

theorem NU.mul {A B : Mat k r} (hA : NU A) (hB : NU B) : NU (A * B) := by
  intro x y hxy
  rw [Matrix.mul_apply, Finset.sum_eq_single x]
  · rw [hA x x le_rfl, hB x y hxy, Matrix.one_apply_eq, one_mul]
  · intro z _ hzx
    by_cases hz : lv k r z ≤ lv k r x
    · rw [hA x z hz, Matrix.one_apply_ne (Ne.symm hzx), zero_mul]
    · have hzy : z ≠ y := by rintro rfl; omega
      rw [hB z y (by omega), Matrix.one_apply_ne hzy, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem NU.inv {g : Mat k r} (hg : g ∈ UH (Hpk k r)) (hN : NU g) : NU g⁻¹ := by
  intro x y hxy
  rw [(inv_of_UH hg).1, Hpk_eq, mul_M_apply, M_mul_apply, conjTranspose_apply]
  have h := hN (sg k r y) (sg k r x) (by rw [lv_sg, lv_sg]; omega)
  rw [h]
  by_cases hxy' : x = y
  · subst hxy'
    rw [Matrix.one_apply_eq, Matrix.one_apply_eq, star_one, mul_one, sn_sg, sn_mul_self]
  · have : sg k r y ≠ sg k r x := fun e => hxy' (sg_inj e).symm
    rw [Matrix.one_apply_ne this, Matrix.one_apply_ne hxy', star_zero, mul_zero, zero_mul]

theorem NU_supp {A : Mat k r} (h : NU A) : Supp A (fun a b => a ≤ b) := by
  intro x y hxy
  by_contra hc
  apply hxy
  rw [h x y (by omega), Matrix.one_apply_ne]
  rintro rfl; omega

theorem NU_eq_one {A : Mat k r} (h : NU A) (hs : Supp A (fun a b => b ≤ a)) : A = 1 := by
  ext x y
  by_cases hxy : lv k r y ≤ lv k r x
  · exact h x y hxy
  · have hne : x ≠ y := by rintro rfl; exact hxy le_rfl
    rw [Matrix.one_apply_ne hne]
    by_contra h0
    exact hxy (hs x y h0)

theorem NU_of_Nset {n : Mat k r} (hn : n ∈ Nset k r) : NU n := by
  obtain ⟨hU, hA, hB⟩ := hn
  have hU' : nᴴ * (M k r (sn k r) * n) = M k r (sn k r) := by
    rw [← Matrix.mul_assoc, ← Hpk_eq]; exact hU
  have colA : ∀ (a z : Fin (2 * r + k + 1)), a.val < r → a.val ≤ z.val →
      n z a = if z = a then 1 else 0 := by
    intro a z ha hz
    have h := hA ⟨a.val, ha⟩ z hz
    have e : eI k r ⟨a.val, ha⟩ = a := Fin.ext rfl
    rwa [e] at h
  have key : ∀ (b : ℕ) (bb : Fin (2 * r + k + 1)), bb.val = b → b < r →
      ∀ y : Fin (2 * r + k + 1), r + k < y.val → lv k r y ≤ 2 * r - b →
      n (sg k r bb) y = (1 : Mat k r) (sg k r bb) y := by
    intro b
    induction b using Nat.strong_induction_on with
    | _ b ih =>
    intro bb hbb hb y hy hly
    have e := congrFun (congrFun hU' bb) y
    rw [Matrix.mul_apply, Finset.sum_eq_single bb] at e
    · rw [conjTranspose_apply, colA bb bb (by omega) le_rfl, if_pos rfl, star_one, one_mul,
        M_mul_apply] at e
      have hs : sn k r (sg k r bb) = 1 := by
        have := bb.isLt
        simp only [sn, sg_val]; split_ifs <;> first | rfl | (exfalso; omega)
      rw [hs, one_mul] at e
      rw [e]
      by_cases hyb : y = sg k r bb
      · subst hyb
        simp [M, sg_sg, hs]
      · have h1 : bb ≠ sg k r y := fun h => hyb (by rw [h, sg_sg])
        have h2 : sg k r bb ≠ y := fun h => hyb h.symm
        rw [Matrix.one_apply_ne h2]
        simp only [M, if_neg h1]
    · intro z _ hz
      rw [conjTranspose_apply, M_mul_apply]
      by_cases hzb : b ≤ z.val
      · rw [colA bb z (by omega) (by omega), if_neg hz, star_zero, zero_mul]
      · have hz' : z.val < b := by omega
        have := ih z.val hz' z rfl (by omega) y hy (by omega)
        rw [this, Matrix.one_apply_ne, mul_zero, mul_zero]
        intro hzy
        have h1 := lv_sg (k := k) (r := r) z
        rw [hzy] at h1
        have h2 : lv k r z = z.val := by unfold lv; rw [if_pos (by omega)]
        omega
    · intro h; exact absurd (Finset.mem_univ _) h
  intro x y hxy
  have hx := x.isLt; have hy := y.isLt
  by_cases h1 : y.val < r
  · have hyx : y.val ≤ x.val := by unfold lv at hxy; split_ifs at hxy <;> omega
    rw [colA y x h1 hyx, Matrix.one_apply]
  · by_cases h2 : y.val ≤ r + k
    · have hrx : r ≤ x.val := by unfold lv at hxy; split_ifs at hxy <;> omega
      rw [hB x y (by omega) h2 hrx, Matrix.one_apply]
    · have hx2 : r + k < x.val := by unfold lv at hxy; split_ifs at hxy <;> omega
      have := key (sg k r x).val (sg k r x) rfl (by rw [sg_val]; split_ifs <;> omega) y (by omega)
        (by rw [sg_val]; unfold lv at hxy ⊢; split_ifs at hxy ⊢ <;> omega)
      rwa [sg_sg] at this

end PI.SwBig.GU
