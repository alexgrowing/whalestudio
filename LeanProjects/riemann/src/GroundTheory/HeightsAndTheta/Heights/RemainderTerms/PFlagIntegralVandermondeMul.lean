import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsFlag
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial

noncomputable section

theorem FlagIntegralVandermondeMul.proof (h1 : FlagIntegralTopComponent.Statement)
    (h2 : FlagHomogeneousComponentMul.Statement) (h3 : FlagVandermondeHomogeneous.Statement) :
    FlagIntegralVandermondeMul.Statement := by
  intro f N R
  rw [h1 f N (blockVandermonde f N * R),
    h2 _ (blockVandermonde f N) R (topDegree f N) (topDegree f N) (h3 f N),
    if_pos le_rfl, Nat.sub_self, homogeneousComponent_zero, mul_comm,
    Flag.flagIntegral_C_mul, constantCoeff_eq]

end

end RestTerms

end GroundTheory.Heights₂.Heights
