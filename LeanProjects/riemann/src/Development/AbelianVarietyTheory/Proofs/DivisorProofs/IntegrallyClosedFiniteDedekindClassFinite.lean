import Mathlib

namespace GlobalTheory.IntClosedOrder

theorem numberField_fractionRing (A : Type) [CommRing A] [IsDomain A] [CharZero A]
    [Module.Finite ℤ A] : NumberField (FractionRing A) := by
  haveI : @IsScalarTower ℤ ℚ (FractionRing A) Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    IsScalarTower.of_algebraMap_eq (fun x => by
      rw [eq_intCast (algebraMap ℤ ℚ), map_intCast, eq_intCast])
  haveI : FiniteDimensional ℚ (FractionRing A) :=
    Module.Finite.of_isLocalization ℤ A (nonZeroDivisors ℤ)
  exact {}

theorem isIntegralClosure_int (A : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [Module.Finite ℤ A] : IsIntegralClosure A ℤ (FractionRing A) := by
  haveI : Algebra.IsIntegral ℤ A := Algebra.IsIntegral.of_finite ℤ A
  refine ⟨IsFractionRing.injective A (FractionRing A), fun {x} => ⟨fun hx => ?_, ?_⟩⟩
  · exact (IsIntegrallyClosed.isIntegral_iff (R := A) (K := FractionRing A)).mp
      (IsIntegral.tower_top (A := A) hx)
  · rintro ⟨a, rfl⟩
    exact (Algebra.IsIntegral.isIntegral (R := ℤ) a).algebraMap

theorem isDedekindDomain_and_finite_classGroup : ∀ (A : Type) [CommRing A] [IsDomain A]
    [IsIntegrallyClosed A] [CharZero A] [Module.Finite ℤ A],
    IsDedekindDomain A ∧ Finite (ClassGroup A) := by
  intro A _ _ _ _ _
  haveI := numberField_fractionRing A
  haveI := isIntegralClosure_int A
  haveI : @IsScalarTower ℤ ℚ (FractionRing A) Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    IsScalarTower.of_algebraMap_eq (fun x => by
      rw [eq_intCast (algebraMap ℤ ℚ), map_intCast, eq_intCast])
  refine ⟨IsIntegralClosure.isDedekindDomain ℤ ℚ (FractionRing A) A, ?_⟩
  letI := ClassGroup.fintypeOfAdmissibleOfFinite ℚ (FractionRing A) AbsoluteValue.absIsAdmissible
    (S := A)
  exact Finite.of_fintype _

end GlobalTheory.IntClosedOrder
