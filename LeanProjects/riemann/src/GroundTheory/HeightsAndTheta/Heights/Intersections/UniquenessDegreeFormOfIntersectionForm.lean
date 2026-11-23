import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsArith
import GroundTheory.HeightsAndTheta.Heights.Intersections.IsSmoothHermFubiniStudyO1
import GroundTheory.HeightsAndTheta.Heights.Intersections.IsSmoothHermTensor
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

def ThmIUniquePosDim.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (I J : Family ι),
    IsFamily I → IsFamily J → ∀ (P : Ideal (MRing ι)) (n : ℕ) (L : Fin n → HermLine ι),
      1 ≤ n → IsArithVar P n → AllSmooth L → I P n L = J P n L

theorem IsFamily.isRFamily {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {I : Family ι}
    (h : IsFamily I) : IsRFamily I :=
  IsIntersectionFamily.isRFamily ((IsFamily.equiv I).1 h)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
