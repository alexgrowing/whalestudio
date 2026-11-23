import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory

def NonvanishingDense.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (d : ℕ)
    (f : MRing ι), IsArithVar P d → f ∉ P →
    mcPts P ⊆ closure {z | z ∈ mcPts P ∧ eval z (map (Int.castRingHom ℂ) f) ≠ 0}

end GroundTheory.Heights₂.Heights.HilbertSamuel
