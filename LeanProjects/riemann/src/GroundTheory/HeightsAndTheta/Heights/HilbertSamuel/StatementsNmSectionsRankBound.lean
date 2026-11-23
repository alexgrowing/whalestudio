import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSmallPacking
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def NmSectionsRankBound.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (a : K → ℤ),
    IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    (∀ τ : ℕ, Module.Finite ℤ (chartLatNm y a τ)) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℕ, (Module.finrank ℤ (chartLatNm y a τ) : ℝ) ≤ C * ((τ : ℝ) + 1) ^ D

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
