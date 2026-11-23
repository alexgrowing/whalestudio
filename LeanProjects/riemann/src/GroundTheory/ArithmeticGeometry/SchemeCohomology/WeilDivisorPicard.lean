import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.WeilDivisorInvertible
import GroundTheory.ArithmeticGeometry.SchemeCohomology.Picard

namespace GroundTheory.Arith.SchemeCoh

open CategoryTheory AlgebraicGeometry MonoidalCategory

universe u

variable {X : Scheme.{u}} [IsIntegral X] [IsNoetherian X] [IsLocallyFactorial X]

noncomputable def weilDivisorToPic : WeilDivisor X →+ Additive (Pic X) where
  toFun D := Additive.ofMul (Pic.mk (divisorSheaf D) (isInvertibleSheaf_divisorSheaf D))
  map_zero' := by
    rw [ofMul_eq_zero, ← Pic.mk_unit, Pic.mk_eq_mk_iff]
    exact ⟨divisorSheafZeroIso.symm⟩
  map_add' D E := by
    rw [← ofMul_mul, ← Pic.mk_tensor]
    congr 1
    exact (Pic.mk_eq_mk_iff _ _).mpr ⟨(divisorTensorIso D E).symm⟩

lemma weilDivisorToPic_apply (D : WeilDivisor X) :
    weilDivisorToPic D =
      Additive.ofMul (Pic.mk (divisorSheaf D) (isInvertibleSheaf_divisorSheaf D)) := rfl

theorem ker_weilDivisorToPic : (weilDivisorToPic (X := X)).ker = principalDivisors X := by
  ext D
  rw [AddMonoidHom.mem_ker, weilDivisorToPic_apply, ofMul_eq_zero, Pic.mk_eq_one_iff,
    ← sub_zero D, ← nonempty_divisorSheaf_iso_iff, sub_zero]
  constructor
  · rintro ⟨e⟩
    exact ⟨e ≪≫ divisorSheafZeroIso⟩
  · rintro ⟨e⟩
    exact ⟨e ≪≫ divisorSheafZeroIso.symm⟩

theorem weilDivisorToPic_surjective : Function.Surjective (weilDivisorToPic (X := X)) := by
  intro p
  obtain ⟨L, hL, hp⟩ := Pic.exists_mk (Additive.toMul p)
  obtain ⟨D, ⟨e⟩⟩ := exists_iso_divisorSheaf hL
  refine ⟨D, ?_⟩
  rw [weilDivisorToPic_apply, ← ofMul_toMul p, ← hp]
  congr 1
  exact (Pic.mk_eq_mk_iff _ hL).mpr ⟨e.symm⟩

noncomputable def classGroupEquivPic : ClassGroup X ≃+ Additive (Pic X) :=
  (QuotientAddGroup.quotientAddEquivOfEq ker_weilDivisorToPic.symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective _ weilDivisorToPic_surjective)

end GroundTheory.Arith.SchemeCoh
