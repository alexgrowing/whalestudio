import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Statements
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsFlag
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial Finset

theorem constantCoeff_blockPowerSum (f N k : ℕ) (τ : Fin f) (hk : 1 ≤ k) :
    constantCoeff (blockPowerSum f N k τ) = 0 := by
  simp [blockPowerSum, map_sum, map_pow, constantCoeff_X, zero_pow (show k ≠ 0 by omega)]

theorem FlagIntegralKillsPowerSums.proof (h1 : FlagDividedDifferencePoly.Statement)
    (h2 : FlagSymmetricMulAntisym.Statement) (h3 : FlagPowerSumSymmetric.Statement)
    (h4 : FlagIntegralViaQuotient.Statement) : FlagIntegralKillsPowerSums.Statement := by
  intro f N k τ G hk _
  obtain ⟨R, hR, -⟩ := h1 f N G
  have hA : antisymmetrize f N (blockPowerSum f N k τ * G) =
      blockVandermonde f N * (blockPowerSum f N k τ * R) := by
    rw [h2 f N _ G (h3 f N k τ), hR]
    ring
  rw [h4 f N _ _ hA, map_mul, constantCoeff_blockPowerSum f N k τ hk, zero_mul, mul_zero]

end RestTerms

end GroundTheory.Heights₂.Heights
