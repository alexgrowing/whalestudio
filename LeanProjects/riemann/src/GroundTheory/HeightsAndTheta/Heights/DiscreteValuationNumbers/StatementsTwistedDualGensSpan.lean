import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def TwistedDualGensSpan.Statement : Prop :=
  ∀ (R : Type) [CommRing R] (Ω : Type) [Field Ω] [Algebra R Ω]
    (K : Type) [Fintype K] (ι : K → Type) (y : (Σ k, ι k) → Ω)
    (N : ℕ) (E : Type) [AddCommGroup E] [Module Ω E] (B : ChartBundle R (segreVec y) N E)
    (a : K → ℤ) (M : ℕ) (φ : Fin M → Module.Dual Ω E),
    IsTwistedDualGens y B a φ → ∀ c, segreVec y c ≠ 0 →
      Submodule.span Ω (Set.range φ) = ⊤

end

end GroundTheory.Heights₂.Heights.NumbersDVR
