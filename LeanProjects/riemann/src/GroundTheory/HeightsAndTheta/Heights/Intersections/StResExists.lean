import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.AnalyticResolutionHypothesesProjectiveLine
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open GroundTheory.Heights₂.Heights.NumbersDVR (MRing)

def ResExists.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι ℂ)) (e : ℕ), IsProjVar P e → Nonempty (Res ι P e)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
