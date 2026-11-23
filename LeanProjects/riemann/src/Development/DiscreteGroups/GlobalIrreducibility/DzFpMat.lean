import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.DzRedTil
import GroundTheory.AutomorphicForms.FiniteBruhat

noncomputable section

open Matrix GlobalTheory.SmGL GlobalTheory.Whittaker GlobalTheory.LocLanglands DiscreteGroups.sglob.DzRed

namespace DiscreteGroups.sglob.DzFp

section Ring

variable {R : Type} [CommRing R]

theorem longElt_mul_self (n : ℕ) : longElt n R * longElt n R = 1 := Units.ext (antidiag_mul_self n R)

theorem invT_val_apply {n : ℕ} (z : GL (Fin n) R) (i j : Fin n) :
    ((GlobalTheory.CuspRep.invT n R z : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i j =
      ((z⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) j i := rfl

theorem invT_corner {m : ℕ} (y : GL (Fin m) R) :
    GlobalTheory.CuspRep.invT (m + 1) R (corner y) = corner (GlobalTheory.CuspRep.invT m R y) := by
  ext i j
  rw [invT_val_apply, ← corner_inv]
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => simp [corner_last_last]
    | cast j => simp [corner_last_cs, corner_cs_last]
  | cast i =>
    induction j using Fin.lastCases with
    | last => simp [corner_last_cs, corner_cs_last]
    | cast j => rw [corner_cs_cs, corner_cs_cs, invT_val_apply]

theorem tilde_corner {m : ℕ} (y : GL (Fin m) R) :
    tilde (corner y) = longElt (m + 1) R * corner (longElt m R) * corner (tilde y) := by
  simp only [tilde]
  rw [mul_assoc, ← corner_mul, ← mul_assoc (longElt m R), longElt_mul_self, one_mul, invT_corner]

theorem rev_eq_iff' {n : ℕ} (i j : Fin n) : i = j.rev ↔ j = i.rev :=
  ⟨fun h => by rw [h, Fin.rev_rev], fun h => by rw [h, Fin.rev_rev]⟩

theorem invT_longElt (n : ℕ) : GlobalTheory.CuspRep.invT n R (longElt n R) = longElt n R := by
  ext i j
  rw [invT_val_apply, longElt_inv, val_longElt, val_longElt]
  exact if_congr (rev_eq_iff' i j) rfl rfl

theorem invT_invT {n : ℕ} (y : GL (Fin n) R) : GlobalTheory.CuspRep.invT n R (GlobalTheory.CuspRep.invT n R y) = y := by
  ext i j
  rw [invT_val_apply, show (GlobalTheory.CuspRep.invT n R y)⁻¹ = GlobalTheory.CuspRep.invT n R y⁻¹ from (map_inv _ y).symm,
    invT_val_apply, inv_inv]

theorem tilde_tilde {n : ℕ} (y : GL (Fin n) R) : tilde (tilde y) = y := by
  simp only [tilde, map_mul, invT_longElt, invT_invT, ← mul_assoc, longElt_mul_self, one_mul]

theorem conjT_inv {n : ℕ} (u : GL (Fin n) R) :
    longElt n R * GlobalTheory.CuspRep.invT n R u⁻¹ * (longElt n R)⁻¹ =
      (longElt n R * GlobalTheory.CuspRep.invT n R u * (longElt n R)⁻¹)⁻¹ := by
  rw [map_inv]
  group

theorem columnMatrix_sq_zero {n : ℕ} (a : Fin n → R) (c : Fin n) (ha : a c = 0) :
    Matrix.of (fun r k : Fin n => if k = c then a r else 0) * Matrix.of (fun r k : Fin n => if k = c then a r else 0) =
      0 := by
  ext r k
  simp [Matrix.mul_apply, ha]

def colElt {n : ℕ} (a : Fin n → R) (c : Fin n) (ha : a c = 0) : GL (Fin n) R :=
  ⟨1 + Matrix.of (fun r k => if k = c then a r else 0), 1 - Matrix.of (fun r k => if k = c then a r else 0),
    by rw [add_mul, one_mul, mul_sub, mul_one, columnMatrix_sq_zero a c ha, sub_zero]; abel,
    by rw [sub_mul, one_mul, mul_add, mul_one, columnMatrix_sq_zero a c ha, add_zero]; abel⟩

theorem colElt_val {n : ℕ} (a : Fin n → R) (c : Fin n) (ha : a c = 0) :
    (colElt a c ha : Matrix (Fin n) (Fin n) R) = 1 + Matrix.of (fun r k => if k = c then a r else 0) := rfl

theorem colElt_apply {n : ℕ} (a : Fin n → R) (c : Fin n) (ha : a c = 0) (r k : Fin n) :
    (colElt a c ha : Matrix (Fin n) (Fin n) R) r k = (1 : Matrix (Fin n) (Fin n) R) r k + if k = c then a r else 0 :=
  rfl

theorem colElt_mem {n : ℕ} (a : Fin n → R) (c : Fin n) (ha : a c = 0) (h : ∀ r, c < r → a r = 0) :
    colElt a c ha ∈ unipB R (Fin n) := by
  refine (mem_unipB R).2 ⟨fun i j hji => ?_, fun i => ?_⟩
  · rw [colElt_apply, Matrix.one_apply_ne (ne_of_gt hji)]
    by_cases hj : j = c
    · subst hj; simp [h i hji]
    · simp [hj]
  · rw [colElt_apply, Matrix.one_apply_eq]
    by_cases hi : i = c
    · subst hi; simp [ha]
    · simp [hi]

theorem superDiag_colElt {m : ℕ} (a : Fin (m + 1) → R) (i : Fin m) (ha : a i.succ = 0) :
    superDiag (colElt a i.succ ha) = a i.castSucc := by
  have key : ∀ r k : Fin (m + 1), (if k.val = r.val + 1 then (colElt a i.succ ha : Matrix (Fin (m + 1)) (Fin (m + 1)) R) r k
      else 0) = if r = i.castSucc then (if k = i.succ then a r else 0) else 0 := by
    intro r k
    rw [colElt_apply]
    by_cases h1 : k.val = r.val + 1
    · have hrk : r ≠ k := fun h => by rw [h] at h1; omega
      rw [if_pos h1, Matrix.one_apply_ne hrk, zero_add]
      by_cases h2 : k = i.succ
      · have : r = i.castSucc := Fin.ext (by rw [h2, Fin.val_succ] at h1; rw [Fin.val_castSucc]; omega)
        rw [if_pos this]
      · rw [if_neg h2]; split_ifs <;> rfl
    · rw [if_neg h1]
      by_cases h3 : r = i.castSucc
      · by_cases h2 : k = i.succ
        · exact absurd (by rw [h2, h3, Fin.val_succ, Fin.val_castSucc]) h1
        · rw [if_pos h3, if_neg h2]
      · rw [if_neg h3]
  simp only [superDiag, Finset.sum_filter, key]
  simp

theorem colElt_comm {n : ℕ} (Y : GL (Fin n) R) (c j : Fin n) (s : R)
    (hrow : ∀ k, (Y : Matrix (Fin n) (Fin n) R) c k = (1 : Matrix (Fin n) (Fin n) R) c k)
    (h1 : s * (Y : Matrix (Fin n) (Fin n) R) c j = 0) (h2 : (Pi.single j s : Fin n → R) c = 0) :
    colElt (fun r => s * (Y : Matrix (Fin n) (Fin n) R) r j) c h1 * Y = Y * colElt (Pi.single j s) c h2 := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, colElt_val, colElt_val, add_mul, mul_add, one_mul, mul_one]
  congr 1
  ext r k
  simp only [Matrix.mul_apply, Matrix.of_apply, ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  rw [hrow]
  by_cases hk : k = c
  · subst hk
    simp [Pi.single_apply, Matrix.one_apply_eq]
    ring
  · simp [hk, Matrix.one_apply_ne (Ne.symm hk)]

theorem eq_one_of_unip_lower {n : ℕ} {g : GL (Fin n) R} (hu : g ∈ unipB R (Fin n))
    (hb : ∀ i j : Fin n, i < j → (g : Matrix (Fin n) (Fin n) R) i j = 0) : g = 1 := by
  have h := (mem_unipB R).1 hu
  ext i j
  rcases lt_trichotomy i j with hij | rfl | hij
  · rw [hb i j hij, Units.val_one, Matrix.one_apply_ne (ne_of_lt hij)]
  · rw [h.2 i, Units.val_one, Matrix.one_apply_eq]
  · rw [h.1 i j hij, Units.val_one, Matrix.one_apply_ne (ne_of_gt hij)]

end Ring

section Field

variable {k : Type} [Field k]

variable (k) in

def lowB (n : ℕ) : Subgroup (GL (Fin n) k) where
  carrier := {g | (g : Matrix (Fin n) (Fin n) k).BlockTriangular OrderDual.toDual}
  mul_mem' {a b} ha hb := by
    show ((a * b : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).BlockTriangular _
    rw [Units.val_mul]
    exact BlockTriangular.mul ha hb
  one_mem' := by
    show ((1 : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).BlockTriangular _
    rw [Units.val_one]
    exact blockTriangular_one
  inv_mem' {a} ha := by
    show ((a⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).BlockTriangular _
    rw [Matrix.coe_units_inv]
    let _ := (Units.isUnit a).invertible
    exact blockTriangular_inv_of_blockTriangular ha

theorem mem_lowB {n : ℕ} {g : GL (Fin n) k} :
    g ∈ lowB k n ↔ ∀ i j : Fin n, i < j → (g : Matrix (Fin n) (Fin n) k) i j = 0 :=
  ⟨fun h i j hij => h hij, fun h _ _ hij => h _ _ hij⟩

theorem longElt_eq_permGL (n : ℕ) : longElt n k = GroundTheory.Automorphic.permGL k Fin.revPerm := by
  ext i j
  rw [GroundTheory.Automorphic.permGL_apply, val_longElt, Fin.revPerm_apply]
  exact if_congr (rev_eq_iff' j i) rfl rfl

theorem permConj_apply {n : ℕ} (σ : Equiv.Perm (Fin n)) (M : GL (Fin n) k) (r c : Fin n) :
    (((GroundTheory.Automorphic.permGL k σ)⁻¹ * M * GroundTheory.Automorphic.permGL k σ : GL (Fin n) k) :
      Matrix (Fin n) (Fin n) k) r c = (M : Matrix (Fin n) (Fin n) k) (σ r) (σ c) := by
  rw [← map_inv, Units.val_mul, Units.val_mul, GroundTheory.Automorphic.mul_permGL_apply,
    GroundTheory.Automorphic.permGL_mul_apply, inv_inv]

theorem exists_descent {k' : ℕ} (π : Equiv.Perm (Fin (k' + 1))) (h : π ≠ 1) :
    ∃ i : Fin k', π i.succ < π i.castSucc := by
  by_contra hne
  push_neg at hne
  have hmono : StrictMono π := Fin.strictMono_iff_lt_succ.2 fun i =>
    lt_of_le_of_ne (hne i) (π.injective.ne (ne_of_lt Fin.castSucc_lt_succ))
  have hle : ∀ x, x ≤ π x := fun x => hmono.le_apply
  apply h
  have : π⁻¹ = 1 := GroundTheory.Automorphic.perm_eq_one_of_forall_le π⁻¹ fun y => by
    have := hle (π⁻¹ y)
    simpa using this
  exact inv_eq_one.mp this

end Field

end DiscreteGroups.sglob.DzFp
