import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo

def IntegralAgainstPositive.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P P0 : Ideal (MRing ι)) (e : ℕ)
    (L : Fin e → HermLine ι) (g : ((Σ k, ι k) → ℂ) → ℝ),
    P0 ≤ P → (∀ j, IsSemipositiveRel P0 P (L j)) → (∀ z ∈ mcPts P, g z ≤ 0) →
    ptsIntegral P (pot L) g ≤ 0

end GroundTheory.Heights₂.Heights.HilbertSamuel
