import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

noncomputable section

def InjectiveHolomorphicDerivNeZero.Statement : Prop :=
  ∀ (D : Set ℂ) (f : ℂ → ℂ), IsOpen D → DifferentiableOn ℂ f D → Set.InjOn f D → ∀ a ∈ D, deriv f a ≠ 0

end

end GroundTheory.Heights₂.Heights
