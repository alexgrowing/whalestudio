import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.AnalyticResolutionHypothesesProjectiveLine
import GroundTheory.HeightsAndTheta.Heights.Intersections.CompsDim
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open GroundTheory.Heights₂.Heights.NumbersDVR (MRing)

def ZIntPoint.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι ℂ)) (φ : Fin 0 → MCone ι → ℝ),
    IsProjVar P 0 → Nonempty (Res ι P 0) → zInt P 0 φ (fun _ => 1) = 1

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
