import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsCN
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open GroundTheory.Heights₂.Heights.NumbersDVR

def DegLTGrowth.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (n : ℕ) (g : (K → ℤ) → ℤ), DegLT g n →
    ∃ (a₀ : ℕ) (C : ℝ), ∀ a : K → ℕ, (∀ k, a₀ ≤ a k) →
      |(g (fun k => (a k : ℤ)) : ℝ)| ≤ C * ((∑ k, (a k : ℝ)) + 1) ^ ((n : ℝ) - 1)

end GroundTheory.Heights₂.Heights.HilbertSamuel
