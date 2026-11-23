import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Statements
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsFlag
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.FlagBasic
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial

theorem FlagIntegralTopDegree.proof (h1 : FlagAltTopDegree.Statement)
    (h2 : FlagAntisymHomogeneous.Statement) (h3 : FlagIntegralViaQuotient.Statement) :
    FlagIntegralTopDegree.Statement := by
  intro f N H hH
  obtain ⟨e, he⟩ := h1 f N (antisymmetrize f N H) (isBlockAlternating_antisymmetrize f N H)
    (h2 f N H _ hH)
  have hI := h3 f N H (C e) (by rw [he, mul_comm])
  rw [constantCoeff_C] at hI
  have hΔ : algebraMap (RootRing f N) (FractionRing (RootRing f N)) (blockVandermonde f N) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (RootRing f N) (FractionRing (RootRing f N)))).mpr
      (Flag.blockVandermonde_ne_zero f N)
  have hdd : dividedDifference f N H = algebraMap ℚ (FractionRing (RootRing f N)) e := by
    rw [dividedDifference, he, map_mul, mul_div_assoc, div_self hΔ, mul_one,
      IsScalarTower.algebraMap_apply ℚ (RootRing f N) (FractionRing (RootRing f N)),
      MvPolynomial.algebraMap_eq]
  rw [hdd, ← map_mul, hI]

end RestTerms

end GroundTheory.Heights₂.Heights
