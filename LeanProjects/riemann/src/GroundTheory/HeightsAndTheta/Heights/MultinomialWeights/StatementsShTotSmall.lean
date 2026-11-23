import Mathlib
import GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.StatementsEnd
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.TheoremB

open MvPolynomial Finset

def ShTotInvertiblePairSmall.Statement : Prop :=
  ∀ d : IndexData, 0 < d.f → ¬ d.TextRange →
    ∃ F1 F2 : XPoly d, F1.IsHomogeneous (d.D + 1) ∧ F2.IsHomogeneous (d.D + 1) ∧
      shSum d F1 * totSum d F2 - totSum d F1 * shSum d F2 ≠ 0

end GroundTheory.Heights₂.Heights.TheoremB
