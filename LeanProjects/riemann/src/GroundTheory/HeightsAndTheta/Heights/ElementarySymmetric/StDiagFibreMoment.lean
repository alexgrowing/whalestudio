import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsAntisym
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

def DiagFibreMoment.Statement : Prop :=
  ∀ (D : ℕ) (S : ProjectiveLineBundle D) (X A : HermLine S.YIdx) (X₀ X₁ A₀ : HermLine S.WIdx),
    S.IsXi X → IsSmoothHerm A → IsFromBase A → IsPullHerm (diagonalBlockIndex 0) (T.yyEmb 0) X X₀ →
    IsPullHerm (diagonalBlockIndex 1) (T.yyEmb 1) X X₁ → IsPullHerm (diagonalBlockIndex 0) (T.yyEmb 0) A A₀ →
    ∀ k : ℕ, 1 ≤ k → 2 * k ≤ D + 1 →
      ∑ i ∈ Finset.range k, diagInt S.WW S.g S.h X₀ X₁ (word D k i X₀ X₁ A₀) =
        -kappa k * ptsIntegral S.WW
          (pot (Fin.cons X₀ (mix (2 * k - 1) X₁ A₀ : Fin D → HermLine S.WIdx) : Fin (D + 1) → HermLine S.WIdx))
          (fun _ => 1)

end

end GroundTheory.Heights₂.Heights.Inter
