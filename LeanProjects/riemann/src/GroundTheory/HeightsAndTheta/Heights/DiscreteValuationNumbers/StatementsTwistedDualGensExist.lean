import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsSegreClosureNumber
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def TwistedDualGensExist.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsNoetherianRing O] (Ω : Type) [Field Ω] [Algebra O Ω]
    (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (y : (Σ k, ι k) → Ω)
    (N : ℕ) (E : Type) [AddCommGroup E] [Module Ω E] (B : ChartBundle O (segreVec y) N E),
    ∃ a₁ : K → ℤ, ∀ a : K → ℤ, a₁ ≤ a →
      ∃ (M : ℕ) (φ : Fin M → Module.Dual Ω E), IsTwistedDualGens y B a φ

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
