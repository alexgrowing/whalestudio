import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.IsSmoothHermFubiniStudyO1
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

def RatioAlgDep.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Q : Ideal (MRing ι)) (d : ℕ)
    (c : ∀ k, ι k) (p : Fin d → Σ k, ι k),
    IsArithVar Q d →
    ∃ f : MvPolynomial (Fin d) ℤ, f ≠ 0 ∧
      ∀ z : (Σ k, ι k) → ℂ, (∀ g ∈ Q, eval z (map (Int.castRingHom ℂ) g) = 0) →
        (∀ k, z ⟨k, c k⟩ ≠ 0) →
          eval (fun j => z (p j) / z ⟨(p j).1, c (p j).1⟩) (map (Int.castRingHom ℂ) f) = 0

end GroundTheory.Heights₂.Heights.Inter
