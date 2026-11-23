import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.AnalyticResolutionHypothesesProjectiveLine
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open GroundTheory.Heights₂.Heights.NumbersDVR (MRing)

def ZIntAdd.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι ℂ)) (e : ℕ) (L : Fin e → HLine ι) (A B : HLine ι),
    IsProjVar P (e + 1) → Nonempty (Res ι P (e + 1)) → (∀ j, IsSmoothMetric P (L j)) →
    IsSmoothMetric P A → IsSmoothMetric P B →
    zInt P (e + 1) (Fin.cons (logH (ReciprocityTheory.ChartRestriction.G.Geo.HermLine.tensor A B)) fun j => logH (L j))
        (fun _ => 1) =
      zInt P (e + 1) (Fin.cons (logH A) fun j => logH (L j)) (fun _ => 1) +
        zInt P (e + 1) (Fin.cons (logH B) fun j => logH (L j)) (fun _ => 1)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
