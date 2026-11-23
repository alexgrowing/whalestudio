import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def SecMRankBound.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (b : K → ℕ),
    IsArithVar (mCoordIdeal y) (D + 1) → (∀ k, 1 ≤ b k) →
    (∀ m : ℕ, Module.Finite ℤ (secM y (fun k => m * b k))) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, (Module.finrank ℤ (secM y (fun k => m * b k)) : ℝ) ≤ C * ((m : ℝ) + 1) ^ D

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
