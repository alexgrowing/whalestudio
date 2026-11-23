import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffNormFormOfFamilyMemRangeIntegrallyClosed
import Mathlib
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FamIdeal
open AlgebraicGeometry CategoryTheory Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_normFormOfFamily_mem_range_integrallyClosed : ∀ (A K L : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Field K] [Field L] [Algebra A K]
    [IsFractionRing A K] [Algebra K L] [FiniteDimensional K L] [Algebra A L] [IsScalarTower A K L] {m : ℕ}
    (x : Fin m → L), (∀ i, IsIntegral A (x i)) →
    ∀ s, (GlobalTheory.NormSheaf.normForm K L x).coeff s ∈ (algebraMap A K).range := by
  first | exact @GlobalTheory.NormSheaf.IntegralCoeff.coeff_normForm_mem_range | exact GlobalTheory.NormSheaf.IntegralCoeff.coeff_normForm_mem_range | (intros; apply GlobalTheory.NormSheaf.IntegralCoeff.coeff_normForm_mem_range <;> assumption)
