import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsAntisym
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsFibreLocal
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MeasureTheory MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

def diagWordMomentPoly (k i : ℕ) : MvPolynomial (Fin 3) ℝ :=
  momentPoly (sphereMeasure.prod sphereMeasure)
    (fun p : S2 × S2 => (1 / 2 : ℝ) * Real.log ((1 - inner ℝ (p.1 : E3) (p.2 : E3)) / 2))
    (aeval ![dotPoly (Prod.fst : S2 × S2 → S2), dotPoly Prod.snd]
      (pderiv 0 (pderiv 1 ((X 0 - X 1) * X 0 ^ (2 * i) * X 1 ^ (2 * k - 1 - 2 * i) : MvPolynomial (Fin 2) ℝ))))

def DiagFibreFubini.Statement : Prop :=
  ∀ (D : ℕ) (S : ProjectiveLineBundle D) (X A : HermLine S.YIdx) (X₀ X₁ A₀ : HermLine S.WIdx),
    S.IsXi X → IsSmoothHerm A → IsFromBase A → IsPullHerm (diagonalBlockIndex 0) (T.yyEmb 0) X X₀ →
    IsPullHerm (diagonalBlockIndex 1) (T.yyEmb 1) X X₁ → IsPullHerm (diagonalBlockIndex 0) (T.yyEmb 0) A A₀ →
    ∀ k : ℕ, 1 ≤ k → 2 * k ≤ D + 1 →
      ∃ Λ : MvPolynomial (Fin 3) ℝ →ₗ[ℝ] ℝ,
        (∀ i < k, diagInt S.WW S.g S.h X₀ X₁ (word D k i X₀ X₁ A₀) =
          2 ^ (2 * k) * Λ (diagWordMomentPoly k i)) ∧
        ptsIntegral S.WW
            (pot (Fin.cons X₀ (mix (2 * k - 1) X₁ A₀ : Fin D → HermLine S.WIdx) : Fin (D + 1) → HermLine S.WIdx))
            (fun _ => 1) =
          -(2 ^ (2 * k) * Λ (pushMomentPoly k))

end

end GroundTheory.Heights₂.Heights.Inter
