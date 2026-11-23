import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsCurrent
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets

noncomputable section

def SmallSetBallCover.Statement : Prop :=
  ∀ (n d : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)) (K : Set (Fin n → ℂ)),
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ I) < (d : ℕ) → IsCompact K →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ r ∈ Set.Ioc (0 : ℝ) 1, ∃ T : Finset (Fin n → ℂ),
        (↑T : Set (Fin n → ℂ)) ⊆ zeroSet I ∩ K ∧ zeroSet I ∩ K ⊆ ⋃ c ∈ T, Metric.ball c r ∧
          (T.card : ℝ) * r ^ (2 * d) ≤ C * r ^ 2

end

end GroundTheory.Heights₂.Heights
