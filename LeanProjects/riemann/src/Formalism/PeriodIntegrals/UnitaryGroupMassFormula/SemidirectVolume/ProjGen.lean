import Mathlib
import Formalism.SatakeDualWeyl.Statement

noncomputable section

namespace PI.VolSemiDirect.W.PG

open Formalism.UG

structure Dat (A : Type) [CommRing A] (n : Type) (r : ℕ) where
  σA : A →+* A
  JA : Matrix n n A
  e : Fin r → n → A
  f : Fin r → n → A
  z : n → A
  tz : A

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] {r : ℕ}

namespace Dat

variable (D : Dat A n r)

def h (x y : n → A) : A := hform D.σA D.JA x y

def hL (x : n → A) : (n → A) →ₗ[A] A where
  toFun y := D.h x y
  map_add' y y' := by
    simp only [h, hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c y := by
    simp only [h, hform, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hL_apply (x y : n → A) : D.hL x y = D.h x y := rfl

theorem h_add_right (x y y' : n → A) : D.h x (y + y') = D.h x y + D.h x y' := by
  simpa only [hL_apply] using (D.hL x).map_add y y'

theorem h_smul_right (x y : n → A) (c : A) : D.h x (c • y) = c * D.h x y := by
  simpa only [hL_apply, smul_eq_mul] using (D.hL x).map_smul c y

theorem h_sub_right (x y y' : n → A) : D.h x (y - y') = D.h x y - D.h x y' := by
  simpa only [hL_apply] using (D.hL x).map_sub y y'

theorem h_zero_right (x : n → A) : D.h x 0 = 0 := by
  simpa only [hL_apply] using (D.hL x).map_zero

theorem h_sum_right {ι : Type} (s : Finset ι) (x : n → A) (y : ι → n → A) :
    D.h x (∑ i ∈ s, y i) = ∑ i ∈ s, D.h x (y i) := by
  simpa only [hL_apply] using map_sum (D.hL x) y s

theorem h_add_left (x x' y : n → A) : D.h (x + x') y = D.h x y + D.h x' y := by
  simp only [h, hform, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

theorem h_smul_left (x y : n → A) (c : A) : D.h (c • x) y = D.σA c * D.h x y := by
  simp only [h, hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem h_zero_left (y : n → A) : D.h 0 y = 0 := by
  simp [h, hform]

theorem h_sub_left (x x' y : n → A) : D.h (x - x') y = D.h x y - D.h x' y := by
  simp only [h, hform, Pi.sub_apply, map_sub, sub_mul, Finset.sum_sub_distrib]

theorem h_sum_left {ι : Type} (s : Finset ι) (x : ι → n → A) (y : n → A) :
    D.h (∑ i ∈ s, x i) y = ∑ i ∈ s, D.h (x i) y := by
  exact map_sum (AddMonoidHom.mk' (fun x => D.h x y) fun a b => D.h_add_left a b y) x s

structure Hyp : Prop where
  σσ : ∀ x, D.σA (D.σA x) = x
  herm : ∀ i j, D.σA (D.JA j i) = D.JA i j
  ee : ∀ a b, D.h (D.e a) (D.e b) = 0
  ff : ∀ a b, D.h (D.f a) (D.f b) = 0
  ef : ∀ a b, D.h (D.e a) (D.f b) = if a = b then 1 else 0
  ez : ∀ a, D.h (D.e a) D.z = 0
  fz : ∀ a, D.h (D.f a) D.z = 0
  zz : D.tz * D.h D.z D.z = 1

variable {D}

theorem h_symm (H : D.Hyp) (x y : n → A) : D.h y x = D.σA (D.h x y) := by
  simp only [h, hform, map_sum, map_mul, H.σσ, H.herm]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem fe (H : D.Hyp) (a b : Fin r) : D.h (D.f a) (D.e b) = if a = b then 1 else 0 := by
  rw [h_symm H, H.ef b a]
  by_cases hab : a = b
  · subst hab
    simp
  · simp [hab, Ne.symm hab]

theorem ze (H : D.Hyp) (a : Fin r) : D.h D.z (D.e a) = 0 := by
  rw [h_symm H, H.ez, map_zero]

theorem zf (H : D.Hyp) (a : Fin r) : D.h D.z (D.f a) = 0 := by
  rw [h_symm H, H.fz, map_zero]

variable (D)

def pX : (n → A) →ₗ[A] (n → A) := ∑ a, (D.hL (D.f a)).smulRight (D.e a)

def pXv : (n → A) →ₗ[A] (n → A) := ∑ a, (D.hL (D.e a)).smulRight (D.f a)

def pz : (n → A) →ₗ[A] (n → A) := (D.tz • D.hL D.z).smulRight D.z

def pU : (n → A) →ₗ[A] (n → A) := D.pX + D.pXv + D.pz

def pW : (n → A) →ₗ[A] (n → A) := LinearMap.id - D.pU

def Pi (S : (n → A) →ₗ[A] (n → A)) : (n → A) →ₗ[A] (n → A) := D.pU + D.pW ∘ₗ S ∘ₗ D.pW

theorem pX_apply (v : n → A) : D.pX v = ∑ a, D.h (D.f a) v • D.e a := by
  simp only [pX, LinearMap.sum_apply, LinearMap.smulRight_apply, hL_apply]

theorem pXv_apply (v : n → A) : D.pXv v = ∑ a, D.h (D.e a) v • D.f a := by
  simp only [pXv, LinearMap.sum_apply, LinearMap.smulRight_apply, hL_apply]

theorem pz_apply (v : n → A) : D.pz v = (D.tz * D.h D.z v) • D.z := by
  simp only [pz, LinearMap.smulRight_apply, LinearMap.smul_apply, hL_apply, smul_eq_mul]

theorem pU_apply (v : n → A) : D.pU v = D.pX v + D.pXv v + D.pz v := rfl

theorem pW_apply (v : n → A) : D.pW v = v - D.pU v := rfl

theorem Pi_apply (S : (n → A) →ₗ[A] (n → A)) (v : n → A) :
    D.Pi S v = D.pU v + D.pW (S (D.pW v)) := rfl

variable {D}

theorem h_e_pU (H : D.Hyp) (a : Fin r) (v : n → A) : D.h (D.e a) (D.pU v) = D.h (D.e a) v := by
  simp [pU_apply, pX_apply, pXv_apply, pz_apply, h_add_right, h_sum_right, h_smul_right, H.ee, H.ef, H.ez]

theorem h_f_pU (H : D.Hyp) (a : Fin r) (v : n → A) : D.h (D.f a) (D.pU v) = D.h (D.f a) v := by
  simp [pU_apply, pX_apply, pXv_apply, pz_apply, h_add_right, h_sum_right, h_smul_right, fe H, H.ff, H.fz]

theorem h_z_pU (H : D.Hyp) (v : n → A) : D.h D.z (D.pU v) = D.h D.z v := by
  simp only [pU_apply, pX_apply, pXv_apply, pz_apply, h_add_right, h_sum_right, h_smul_right, ze H, zf H,
    mul_zero, Finset.sum_const_zero, zero_add]
  linear_combination (D.h D.z v) * H.zz

def IsW (D : Dat A n r) (w : n → A) : Prop :=
  (∀ a, D.h (D.e a) w = 0) ∧ (∀ a, D.h (D.f a) w = 0) ∧ D.h D.z w = 0

theorem isW_pW (H : D.Hyp) (v : n → A) : IsW D (D.pW v) := by
  exact ⟨fun a => by rw [pW_apply, h_sub_right, h_e_pU H, sub_self],
    fun a => by rw [pW_apply, h_sub_right, h_f_pU H, sub_self],
    by rw [pW_apply, h_sub_right, h_z_pU H, sub_self]⟩

theorem pU_of_isW {w : n → A} (hw : IsW D w) : D.pU w = 0 := by
  obtain ⟨he, hf, hz⟩ := hw
  simp [pU_apply, pX_apply, pXv_apply, pz_apply, he, hf, hz]

theorem pW_of_isW {w : n → A} (hw : IsW D w) : D.pW w = w := by
  rw [pW_apply, pU_of_isW hw, sub_zero]

theorem pU_pU (H : D.Hyp) (v : n → A) : D.pU (D.pU v) = D.pU v := by
  rw [pU_apply D (D.pU v), pX_apply D (D.pU v), pXv_apply D (D.pU v), pz_apply D (D.pU v)]
  simp only [h_f_pU H, h_e_pU H, h_z_pU H]
  rw [← pX_apply, ← pXv_apply, ← pz_apply, ← pU_apply]

theorem pU_pW (H : D.Hyp) (v : n → A) : D.pU (D.pW v) = 0 := pU_of_isW (isW_pW H v)

theorem pW_pW (H : D.Hyp) (v : n → A) : D.pW (D.pW v) = D.pW v := pW_of_isW (isW_pW H v)

theorem pW_pU (H : D.Hyp) (v : n → A) : D.pW (D.pU v) = 0 := by
  rw [pW_apply, pU_pU H, sub_self]

theorem pU_e (H : D.Hyp) (b : Fin r) : D.pU (D.e b) = D.e b := by
  simp [pU_apply, pX_apply, pXv_apply, pz_apply, fe H, H.ee, ze H, ite_smul]

theorem pU_f (H : D.Hyp) (b : Fin r) : D.pU (D.f b) = D.f b := by
  simp [pU_apply, pX_apply, pXv_apply, pz_apply, H.ff, H.ef, zf H, ite_smul]

theorem pU_z_eq (H : D.Hyp) : D.pU D.z = D.z := by
  simp [pU_apply, pX_apply, pXv_apply, pz_apply, H.fz, H.ez, H.zz]

theorem pW_e (H : D.Hyp) (b : Fin r) : D.pW (D.e b) = 0 := by
  rw [pW_apply, pU_e H, sub_self]

theorem pW_f (H : D.Hyp) (b : Fin r) : D.pW (D.f b) = 0 := by
  rw [pW_apply, pU_f H, sub_self]

theorem orthogonal_proj_normal_zero (H : D.Hyp) : D.pW D.z = 0 := by
  rw [pW_apply, pU_z_eq H, sub_self]

theorem pW_pX (H : D.Hyp) (u : n → A) : D.pW (D.pX u) = 0 := by
  rw [pX_apply]
  simp [map_sum, map_smul, pW_e H]

end Dat

end PI.VolSemiDirect.W.PG
