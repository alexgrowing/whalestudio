import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.FlagIntegralRealRootRingToRealAlt
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PRestPolynomialHomogeneous
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PVandermondeOfHomogeneous
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

noncomputable section

def SmallBlockTermBound.Statement : Prop :=
  ∀ (f r a : ℕ) (c : SmallBlock), 1 ≤ f → 1 ≤ r → 1 ≤ a → r ≤ a →
    ∀ Q : ℕ → Fin f → RootRing f (r + a),
      IsPowerSumDecomposition f (r + a) (restPolynomial f r a c) Q →
      ∀ k : ℕ, 2 ≤ k → k ≤ r + a → ∀ τ τ' : Fin f,
        |restTerm f (r + a) Q k τ (smallPowerSum f r a c (k - 1) τ')| ≤
          ((f * (r * a) + 1 : ℕ) : ℚ) * |fibreDegree f r a c| * restX r a ^ (k - 1) /
            (k.factorial : ℚ)

namespace TermBoundEq

end TermBoundEq

open TermBoundEq

end

end GroundTheory.Heights₂.Heights.RestTerms
