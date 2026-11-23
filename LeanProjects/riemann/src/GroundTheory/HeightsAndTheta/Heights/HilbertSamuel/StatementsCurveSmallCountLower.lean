import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ImportsFurther
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def CurveSmallCountLower.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (A : HermLine ι) (II : IntersectionSystem),
    IsIntersectionSystem II → IsArithVar (mCoordIdeal y) 1 → Birational y →
    IsSmoothHerm A → IsConjInvariantH A →
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
      (n : ℝ) * II K ι (mCoordIdeal y) 1 (fun _ => A) - C ≤
        smallSectionCount (IsSmallH (mCoordIdeal y) y A) (chartLat y A.a) n

namespace CurveSmallCountLower

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet

end CurveSmallCountLower

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
