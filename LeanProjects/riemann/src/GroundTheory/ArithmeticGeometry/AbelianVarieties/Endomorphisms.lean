import Mathlib
import GroundTheory.ArithmeticGeometry.AbelianVarieties.DualQuadratic

namespace GroundTheory.Arith.Abelian

open Polynomial WeierstrassCurve WeierstrassCurve.Affine

universe u

variable {F : Type u} [Field F] [IsAlgClosed F] [DecidableEq F] {E : WeierstrassCurve F}
  [E.IsElliptic]

noncomputable def endDual : isogEnd E →+ isogEnd E := homDual

noncomputable def endDeg (a : isogEnd E) : ℤ := homDeg a

noncomputable def endTrace (a : isogEnd E) : ℤ := degBilin a 1

theorem zsmul_homId_eq_intCast (n : ℤ) : n • (homId : isogEnd E) = (n : isogEnd E) :=
  zsmul_one n

theorem intCast_isogEnd_eq_zero {n : ℤ} (h : (n : isogEnd E) = 0) : n = 0 :=
  eq_zero_of_zsmul_homId (E := E) (by rw [zsmul_homId_eq_intCast, h])

theorem intCast_isogEnd_injective : Function.Injective (Int.cast : ℤ → isogEnd E) := by
  intro m n h
  have : ((m - n : ℤ) : isogEnd E) = 0 := by rw [Int.cast_sub, h, sub_self]
  exact sub_eq_zero.mp (intCast_isogEnd_eq_zero this)

instance : CharZero (isogEnd E) where
  cast_injective m n h := by
    have : ((m : ℤ) : isogEnd E) = ((n : ℤ) : isogEnd E) := by
      rw [Int.cast_natCast, Int.cast_natCast]; exact h
    exact_mod_cast intCast_isogEnd_injective this

theorem isogEnd_one_eq_mulIsogeny :
    (1 : isogEnd E) = (mulIsogeny E 1 one_ne_zero).toHom := by
  rw [mulIsogeny_toHom, one_smul]; rfl

theorem homPt_one : homPt (1 : isogEnd E) = AddMonoidHom.id E.toAffine.Point := by
  rw [isogEnd_one_eq_mulIsogeny, homPt_toHom]
  ext R
  rw [Isogeny.pointHom_apply, Isogeny.pointMap_mulIsogeny, one_smul]
  rfl

theorem homPt_mul (a b : isogEnd E) : homPt (a * b) = (homPt a).comp (homPt b) := by
  by_cases ha : a = 0
  · rw [ha, zero_mul, homPt_zero, AddMonoidHom.zero_comp]
  by_cases hb : b = 0
  · rw [hb, mul_zero, homPt_zero, AddMonoidHom.comp_zero]
  rw [← isogOfHom_toHom a ha, ← isogOfHom_toHom b hb, isogEnd_mul_def, Isogeny.homComp_toHom,
    homPt_toHom, homPt_toHom, homPt_toHom]
  ext R
  exact Isogeny.pointMap_comp _ _ R

noncomputable def endPointRingHom : isogEnd E →+* AddMonoid.End E.toAffine.Point where
  toFun := homPt
  map_one' := homPt_one
  map_mul' := homPt_mul
  map_zero' := homPt_zero
  map_add' := homPt_add

end GroundTheory.Arith.Abelian
