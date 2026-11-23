import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsArith
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def regularityPointsSum_holds.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)),
    IsArithVar P 1 →
    ∃ R : Finset ((Σ k, ι k) → ℂ), (∀ t ∈ R, t ∈ mcPts P) ∧
      (∀ z ∈ mcPts P, ∃! t, t ∈ R ∧ SameOrbit z t) ∧
      ∀ h : ((Σ k, ι k) → ℂ) → ℝ,
        (∀ z z', z ∈ mcPts P → SameOrbit z z' → h z = h z') →
        ptsIntegral P (Fin.elim0 : Fin 0 → ((Σ k, ι k) → ℂ) → ℝ) h = ∑ t ∈ R, h t

end

end GroundTheory.Heights₂.Heights.Inter
