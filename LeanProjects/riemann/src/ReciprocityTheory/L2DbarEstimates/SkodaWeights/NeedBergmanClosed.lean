import ReciprocityTheory.L2DbarEstimates.SkodaWeights.SkodaWeightStatement

namespace ReciprocityTheory.L2DbarEstimates.H

open MeasureTheory ReciprocityTheory.L2DbarEstimates

def NeedBergmanClosed (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : Prop :=
  ∀ z : M → V n, IsLocalHomeomorph z → ∀ ψ : M → ℝ, Continuous ψ →
    IsClosed (holSub n z ψ : Set (WeightedL2 n z ψ))

end ReciprocityTheory.L2DbarEstimates.H
