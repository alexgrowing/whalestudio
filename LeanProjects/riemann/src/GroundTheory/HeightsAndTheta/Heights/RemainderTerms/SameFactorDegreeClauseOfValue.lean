import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.NumStandardTableTranspose
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset FlagEq DegreeValueAlt

noncomputable section

def SameFactorDegreeClause.Statement : Prop :=
  ∀ (f r a : ℕ) (c : SmallBlock), 1 ≤ f → 1 ≤ r → 1 ≤ a →
    ∃ C₀ : ℚ, C₀ ≠ 0 ∧
      fibreDegree f r a c =
        C₀ * (f * (r * a)).factorial / ((r * a).factorial : ℚ) ^ f *
          (numStandardTable (rectangle r a) : ℚ) ^ f

end

end GroundTheory.Heights₂.Heights.RestTerms
