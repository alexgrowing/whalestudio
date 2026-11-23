import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def ClopenDegree.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ)
    (L : Fin e → HermLine ι) (A : Set ((Σ k, ι k) → ℂ)),
    IsArithVar P (e + 1) → (∀ j, IsSmoothHerm (L j)) → A ⊆ mcPts P →
    IsClopen (((↑) : mcPts P → (Σ k, ι k) → ℂ) ⁻¹' A) →
    ptsIntegral P (pot L) (A.indicator fun _ => (1 : ℝ)) =
      NumbersDVR.intNum ℂ (vanishingIdeal ℂ A) (fun j => (L j).a)

section Inhabitants

open GroundTheory.Heights₂.Heights.Inter

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
