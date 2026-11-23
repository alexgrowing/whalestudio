import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.FiniteAlgebraLocalCompletion

namespace GlobalTheory

theorem integralClosure_finite_local_of_isAdicComplete :
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsIntegrallyClosed R]
      [CharZero R], IsAdicComplete (IsLocalRing.maximalIdeal R) R →
      ∀ (L : Type) [Field L] [Algebra (FractionRing R) L] [FiniteDimensional (FractionRing R) L]
        [Algebra R L] [IsScalarTower R (FractionRing R) L],
        Module.Finite R (integralClosure R L) ∧ IsLocalRing (integralClosure R L) ∧
          IsNoetherianRing (integralClosure R L) ∧ IsIntegrallyClosed (integralClosure R L) ∧
          IsFractionRing (integralClosure R L) L := by
  intro R _ _ _ _ _ _ hR L _ _ _ _ _
  have : CharZero (FractionRing R) := IsFractionRing.charZero_of_isFractionRing R
  have : Algebra.IsSeparable (FractionRing R) L := inferInstance
  have hfin : Module.Finite R (integralClosure R L) :=
    IsIntegralClosure.finite R (FractionRing R) L (integralClosure R L)
  have hfr : IsFractionRing (integralClosure R L) L :=
    integralClosure.isFractionRing_of_finite_extension (FractionRing R) L
  refine ⟨hfin, ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.isLocalRing_finite_domain (R := R) _,
    IsNoetherianRing.of_finite R _, ?_, hfr⟩
  exact (isIntegrallyClosed_iff_isIntegrallyClosedIn L).2 inferInstance

end GlobalTheory
