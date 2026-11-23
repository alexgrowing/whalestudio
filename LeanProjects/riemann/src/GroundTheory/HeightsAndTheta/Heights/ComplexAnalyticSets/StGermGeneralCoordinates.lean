import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StGermWeierstrassDivision
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

noncomputable section

def GeneralLinearCoordinates.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (f : (Option σ → ℂ) → ℂ),
    AnalyticAt ℂ f 0 → ¬ (∀ᶠ x in 𝓝 (0 : Option σ → ℂ), f x = 0) →
    ∃ (A : (Option σ → ℂ) ≃L[ℂ] (Option σ → ℂ)) (d : ℕ),
      analyticOrderAt (fun t => f (A (pointWithLast 0 t))) 0 = d

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
