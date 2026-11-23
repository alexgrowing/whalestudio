import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralClosureFiniteTypeOfCharZero
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralClosure_finiteType_over_adjoin : ∀ (k F K : Type) [Field k] [CharZero k] [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] [FiniteDimensional F K] (d : ℕ) (u : Fin d → F), AlgebraicIndependent k u → ∀ (A : Subalgebra k F) [IsFractionRing A F], A = Algebra.adjoin k (Set.range u) → ∀ (B : Subalgebra k K), B = (integralClosure A K).restrictScalars k → Algebra.FiniteType k B := by
  first | (exact @GlobalTheory.integralClosure_finiteType_of_charZero) | (exact GlobalTheory.integralClosure_finiteType_of_charZero) | (intros; apply GlobalTheory.integralClosure_finiteType_of_charZero  <;> assumption)
