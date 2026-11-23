import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.NoCommonComponentCoordinatesPlane
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

def HorizNotMem.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (d : ℕ)
    (s s' : MRing ι) (W : Ideal (MRing ι)),
    IsArithVar P d → s ∉ P → s' ∉ P →
    (∀ W, W ∈ divSupp P s → W ∈ divSupp P s' → ¬ IsHorizontal W) →
    W ∈ divSupp P s → IsHorizontal W → s' ∉ W

end GroundTheory.Heights₂.Heights.Inter
