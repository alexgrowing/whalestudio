import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.AlgebraMapMemChartRingLine
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

def GlobalFunctionsIntegral.Statement : Prop :=
  ∀ (k : Type u) [Field k] (K : Type w) [Field K] [Algebra k K] (N : ℕ) (y : Fin (N + 1) → K) (a : K),
    y ≠ 0 → (∀ (i : Fin (N + 1)) (hi : y i ≠ 0), a ∈ chartRing k y (singleChart hi)) → IsIntegral k a

end

end GroundTheory.Heights₂.Heights.Kleiman
