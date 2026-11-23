import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory

theorem integralClosure_finiteType_of_charZero :
    ∀ (k F K : Type) [Field k] [CharZero k] [Field F] [Field K] [Algebra k F] [Algebra k K]
      [Algebra F K] [IsScalarTower k F K] [FiniteDimensional F K] (d : ℕ) (u : Fin d → F),
      AlgebraicIndependent k u → ∀ (A : Subalgebra k F) [IsFractionRing A F],
      A = Algebra.adjoin k (Set.range u) → ∀ (B : Subalgebra k K),
      B = (integralClosure A K).restrictScalars k → Algebra.FiniteType k B := by
  intro k F K _ _ _ _ _ _ _ _ _ d u hu A _ hA B hB
  subst hB

  have e : MvPolynomial (Fin d) k ≃ₐ[k] A := by
    subst hA; exact hu.aevalEquiv
  have hAft : Algebra.FiniteType k A := Algebra.FiniteType.equiv inferInstance e
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  have : IsIntegrallyClosed A := IsIntegrallyClosed.of_equiv e.toRingEquiv
  have : CharZero F := charZero_of_injective_algebraMap (algebraMap k F).injective
  have : Algebra.IsSeparable F K := inferInstance
  have : Module.Finite A (integralClosure A K) := IsIntegralClosure.finite A F K (integralClosure A K)
  have : Algebra.FiniteType A (integralClosure A K) := inferInstance
  have : Algebra.FiniteType k (integralClosure A K) := Algebra.FiniteType.trans hAft this
  exact this

end GlobalTheory
