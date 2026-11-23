import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsSegreClosureNumber
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def TwistedDualGensExpress.Statement : Prop :=
  ∀ (R : Type) [CommRing R] (ϖ : R) (Ω : Type) [Field Ω] [Algebra R Ω]
    (K : Type) [Fintype K] (ι : K → Type) (y : (Σ k, ι k) → Ω)
    (N : ℕ) (E : Type) [AddCommGroup E] [Module Ω E] (B B' : ChartBundle R (segreVec y) N E),
    SameGenericFibre ϖ B B' →
    ∀ (a a' : K → ℤ) (M M' : ℕ) (φ : Fin M → Module.Dual Ω E) (φ' : Fin M' → Module.Dual Ω E),
      IsTwistedDualGens y B a φ → IsTwistedDualGens y B' a' φ' →
    ∀ c, segreVec y c ≠ 0 → ∀ m, ∃ (n : ℕ) (r : Fin M → Ω),
      (∀ l, r l ∈ chartRing R (segreVec y) c) ∧
      algebraMap R Ω ϖ ^ n • φ' m = ∑ l, (r l * ∏ k, y ⟨k, c k⟩ ^ (a' k - a k)) • φ l

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
