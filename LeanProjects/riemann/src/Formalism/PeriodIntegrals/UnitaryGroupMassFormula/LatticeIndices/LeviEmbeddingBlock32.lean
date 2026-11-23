import Mathlib
import Formalism.HermitianCurvature.MemParahoricTimesPrincipalCongruenceIff

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace MassDataIdxStIm

open Matrix Finset
open Formalism.DoubleCosetMeasures (IsUpUni upUniG isUpUni_mul isUpUni_inv isUpUni_one isUpUni_det)
open Formalism.FourierDecayAlt.S3

section Blocks

variable {A : Type} {r k : ℕ}

variable [CommRing A]

theorem block11_mul (x y : Matrix (Idx r k) (Idx r k) A) :
    b11 (x * y) = b11 x * b11 y + b12 x * b21 y + b13 x * b31 y := by
  ext a b
  (simp only [b11, b12, b13, b21, b22, b23, b31, b32, b33, Matrix.mul_apply, Matrix.add_apply, Matrix.of_apply, Fintype.sum_sum_type]) <;> ring

theorem one_block11 : b11 (1 : Matrix (Idx r k) (Idx r k) A) = 1 := by
  ext a b
  simp [b11, b12, b13, b21, b22, b23, b31, b32, b33, Matrix.one_apply]

theorem block21_mul (x y : Matrix (Idx r k) (Idx r k) A) :
    b21 (x * y) = b21 x * b11 y + b22 x * b21 y + b23 x * b31 y := by
  ext a b
  (simp only [b11, b12, b13, b21, b22, b23, b31, b32, b33, Matrix.mul_apply, Matrix.add_apply, Matrix.of_apply, Fintype.sum_sum_type]) <;> ring

theorem one_block21 : b21 (1 : Matrix (Idx r k) (Idx r k) A) = 0 := by
  ext a b
  simp [b11, b12, b13, b21, b22, b23, b31, b32, b33, Matrix.one_apply]

theorem block22_mul (x y : Matrix (Idx r k) (Idx r k) A) :
    b22 (x * y) = b21 x * b12 y + b22 x * b22 y + b23 x * b32 y := by
  ext a b
  (simp only [b11, b12, b13, b21, b22, b23, b31, b32, b33, Matrix.mul_apply, Matrix.add_apply, Matrix.of_apply, Fintype.sum_sum_type]) <;> ring

theorem block22_one : b22 (1 : Matrix (Idx r k) (Idx r k) A) = 1 := by
  ext a b
  simp [b11, b12, b13, b21, b22, b23, b31, b32, b33, Matrix.one_apply]

theorem block31_mul (x y : Matrix (Idx r k) (Idx r k) A) :
    b31 (x * y) = b31 x * b11 y + b32 x * b21 y + b33 x * b31 y := by
  ext a b
  (simp only [b11, b12, b13, b21, b22, b23, b31, b32, b33, Matrix.mul_apply, Matrix.add_apply, Matrix.of_apply, Fintype.sum_sum_type]) <;> ring

theorem one_block31 : b31 (1 : Matrix (Idx r k) (Idx r k) A) = 0 := by
  ext a b
  simp [b11, b12, b13, b21, b22, b23, b31, b32, b33, Matrix.one_apply]

theorem block32_mul (x y : Matrix (Idx r k) (Idx r k) A) :
    b32 (x * y) = b31 x * b12 y + b32 x * b22 y + b33 x * b32 y := by
  ext a b
  (simp only [b11, b12, b13, b21, b22, b23, b31, b32, b33, Matrix.mul_apply, Matrix.add_apply, Matrix.of_apply, Fintype.sum_sum_type]) <;> ring

theorem block32_one : b32 (1 : Matrix (Idx r k) (Idx r k) A) = 0 := by
  ext a b
  simp [b11, b12, b13, b21, b22, b23, b31, b32, b33, Matrix.one_apply]

theorem block33_mul (x y : Matrix (Idx r k) (Idx r k) A) :
    b33 (x * y) = b31 x * b13 y + b32 x * b23 y + b33 x * b33 y := by
  ext a b
  (simp only [b11, b12, b13, b21, b22, b23, b31, b32, b33, Matrix.mul_apply, Matrix.add_apply, Matrix.of_apply, Fintype.sum_sum_type]) <;> ring

theorem block33_one : b33 (1 : Matrix (Idx r k) (Idx r k) A) = 1 := by
  ext a b
  simp [b11, b12, b13, b21, b22, b23, b31, b32, b33, Matrix.one_apply]

theorem midEmb_mul (h h' : Matrix (Fin k) (Fin k) A) : midEmb h * midEmb h' = midEmb (h * h') := by
  simp [midEmb, Matrix.fromBlocks_multiply]

theorem midEmb_one : midEmb (1 : Matrix (Fin k) (Fin k) A) = 1 := by
  simp [midEmb, Matrix.fromBlocks_one]

theorem midEmb_inj {h h' : Matrix (Fin k) (Fin k) A} (e : midEmb h = midEmb h') : h = h' := (Matrix.fromBlocks_inj.1 e).1

theorem midEmb_det (h : Matrix (Fin k) (Fin k) A) : (midEmb h).det = h.det := by
  simp [midEmb, Matrix.det_fromBlocks_zero₂₁]

theorem hEmb_mul (h h' : Matrix (Fin k) (Fin k) A) : hEmb r h * hEmb r h' = hEmb r (h * h') := by
  simp [hEmb, Matrix.fromBlocks_multiply, midEmb_mul]

theorem hEmb_one : hEmb r (1 : Matrix (Fin k) (Fin k) A) = 1 := by
  simp [hEmb, midEmb_one, Matrix.fromBlocks_one]

theorem hEmb_inj {h h' : Matrix (Fin k) (Fin k) A} (e : hEmb r h = hEmb r h') : h = h' := by
  have e1 := (Matrix.fromBlocks_inj.1 e).2.2.2
  exact midEmb_inj (Matrix.fromBlocks_inj.1 e1).1

structure GP (P : Matrix (Fin k) (Fin k) A → Prop) : Prop where
  one : P 1
  mul : ∀ {h h'}, P h → P h' → P (h * h')
  inv : ∀ {h}, P h → P h⁻¹
  unit : ∀ {h}, P h → IsUnit h.det

theorem gpUnit : GP (fun h : Matrix (Fin k) (Fin k) A => IsUnit h.det) where
  one := by simp
  mul := by intro h h' a b; rw [Matrix.det_mul]; exact a.mul b
  inv := by intro h a; exact Matrix.isUnit_nonsing_inv_det h a
  unit := fun a => a

theorem gpUni : GP (IsUpUni : Matrix (Fin k) (Fin k) A → Prop) where
  one := isUpUni_one A
  mul := fun a b => isUpUni_mul A a b
  inv := fun a => isUpUni_inv A a
  unit := by intro h a; rw [isUpUni_det A a]; exact isUnit_one

def Par (P : Matrix (Fin k) (Fin k) A → Prop) (x : Matrix (Idx r k) (Idx r k) A) : Prop :=
  IsUpUni (b11 x) ∧ IsUpUni (b33 x) ∧ b21 x = 0 ∧ b31 x = 0 ∧ b32 x = 0 ∧ ∃ h, P h ∧ b22 x = midEmb h

def Emb (P : Matrix (Fin k) (Fin k) A → Prop) (x : Matrix (Idx r k) (Idx r k) A) : Prop :=
  ∃ h, P h ∧ x = hEmb r h

variable {P : Matrix (Fin k) (Fin k) A → Prop}

theorem uni_unit {n : ℕ} {u : Matrix (Fin n) (Fin n) A} (hu : IsUpUni u) : IsUnit u.det := by
  rw [isUpUni_det (K := A) hu]; exact isUnit_one

theorem par_det (hP : GP P) {x : Matrix (Idx r k) (Idx r k) A} (hx : Par P x) : IsUnit x.det := by
  obtain ⟨h1, h3, h21, h31, h32, h, hPh, h22⟩ := hx
  rw [← Matrix.fromBlocks_toBlocks x]
  have hz : x.toBlocks₂₁ = 0 := by
    ext i j
    rcases i with a | a
    · exact congrFun (congrFun h21 a) j
    · exact congrFun (congrFun h31 a) j
  have hD : x.toBlocks₂₂ = Matrix.fromBlocks (b22 x) (b23 x) 0 (b33 x) := by
    ext i j
    rcases i with a | a <;> rcases j with b | b
    · rfl
    · rfl
    · exact congrFun (congrFun h32 a) b
    · rfl
  rw [hz, Matrix.det_fromBlocks_zero₂₁, hD, Matrix.det_fromBlocks_zero₂₁, h22, midEmb_det]
  exact (uni_unit h1).mul ((hP.unit hPh).mul (uni_unit h3))

theorem par_one (hP : GP P) : Par P (1 : Matrix (Idx r k) (Idx r k) A) := by
  refine ⟨?_, ?_, one_block21, one_block31, block32_one, 1, hP.one, ?_⟩
  · rw [one_block11]; exact isUpUni_one (K := A)
  · rw [block33_one]; exact isUpUni_one (K := A)
  · rw [block22_one, midEmb_one]

theorem par_mul (hP : GP P) {x y : Matrix (Idx r k) (Idx r k) A} (hx : Par P x) (hy : Par P y) :
    Par P (x * y) := by
  obtain ⟨x1, x3, x21, x31, x32, h, hh, x22⟩ := hx
  obtain ⟨y1, y3, y21, y31, y32, g, hg, y22⟩ := hy
  refine ⟨?_, ?_, ?_, ?_, ?_, h * g, hP.mul hh hg, ?_⟩
  · rw [block11_mul, y21, y31]; simpa using isUpUni_mul (K := A) x1 y1
  · rw [block33_mul, x31, x32]; simpa using isUpUni_mul (K := A) x3 y3
  · rw [block21_mul, x21, y21, y31]; simp
  · rw [block31_mul, x31, x32, y31]; simp
  · rw [block32_mul, x31, x32, y32]; simp
  · rw [block22_mul, x21, y32, x22, y22, midEmb_mul]; simp

theorem par_rinv (hP : GP P) {x y : Matrix (Idx r k) (Idx r k) A} (hx : Par P x) (e : x * y = 1) :
    Par P y := by
  obtain ⟨x1, x3, x21, x31, x32, h, hh, x22⟩ := hx
  have e' : y * x = 1 := mul_eq_one_comm.1 e
  have u1 := uni_unit x1
  have u2 : IsUnit (b22 x).det := by rw [x22, midEmb_det]; exact hP.unit hh
  have rz : ∀ {m : Type} [Fintype m] [DecidableEq m] {n : Type} {B : Matrix n m A} {C : Matrix m m A},
      IsUnit C.det → B * C = 0 → B = 0 := by
    intro m _ _ n B C hC hBC
    calc B = B * (C * C⁻¹) := by rw [Matrix.mul_nonsing_inv C hC, Matrix.mul_one]
      _ = 0 := by rw [← Matrix.mul_assoc, hBC, Matrix.zero_mul]
  have e11 : b11 y * b11 x = 1 := by
    have t := congrArg b11 e'; rw [block11_mul, x21, x31, one_block11] at t; simpa using t
  have e21 : b21 y * b11 x = 0 := by
    have t := congrArg b21 e'; rw [block21_mul, x21, x31, one_block21] at t; simpa using t
  have e31 : b31 y * b11 x = 0 := by
    have t := congrArg b31 e'; rw [block31_mul, x21, x31, one_block31] at t; simpa using t
  have y21 := rz u1 e21
  have y31 := rz u1 e31
  have e22 : b22 y * b22 x = 1 := by
    have t := congrArg b22 e'; rw [block22_mul, y21, x32, block22_one] at t; simpa using t
  have e32 : b32 y * b22 x = 0 := by
    have t := congrArg b32 e'; rw [block32_mul, y31, x32, block32_one] at t; simpa using t
  have y32 := rz u2 e32
  have e33 : b33 y * b33 x = 1 := by
    have t := congrArg b33 e'; rw [block33_mul, y31, y32, block33_one] at t; simpa using t
  refine ⟨?_, ?_, y21, y31, y32, h⁻¹, hP.inv hh, ?_⟩
  · rw [← Matrix.inv_eq_left_inv e11]; exact isUpUni_inv (K := A) x1
  · rw [← Matrix.inv_eq_left_inv e33]; exact isUpUni_inv (K := A) x3
  · rw [← Matrix.inv_eq_left_inv e22, x22]
    exact Matrix.inv_eq_left_inv (by rw [midEmb_mul, Matrix.nonsing_inv_mul h (hP.unit hh), midEmb_one])

def parG (hP : GP P) : Subgroup (GL (Idx r k) A) where
  carrier := {g | Par P (g : Matrix (Idx r k) (Idx r k) A)}
  one_mem' := by simpa using par_one hP
  mul_mem' := by intro a b ha hb; simpa using par_mul hP ha hb
  inv_mem' := by
    intro a ha
    refine par_rinv hP ha ?_
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]

def embG (hP : GP P) : Subgroup (GL (Idx r k) A) where
  carrier := {g | Emb P (g : Matrix (Idx r k) (Idx r k) A)}
  one_mem' := ⟨1, hP.one, by simp [hEmb_one]⟩
  mul_mem' := by
    rintro a b ⟨h, hh, ea⟩ ⟨g, hg, eb⟩
    exact ⟨h * g, hP.mul hh hg, by rw [Units.val_mul, ea, eb, hEmb_mul]⟩
  inv_mem' := by
    rintro a ⟨h, hh, ea⟩
    refine ⟨h⁻¹, hP.inv hh, ?_⟩
    rw [Matrix.coe_units_inv, ea]
    refine Matrix.inv_eq_right_inv ?_
    rw [hEmb_mul, Matrix.mul_nonsing_inv h (hP.unit hh), hEmb_one]

end Blocks

end MassDataIdxStIm
