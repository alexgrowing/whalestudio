import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsAntisym
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsFibreLocal
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MeasureTheory MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

def wwLinPot {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {e : ℕ} (X₀ X₁ A₀ : HermLine ι) (k : ℕ)
    (u : ℕ → Fin 2 → ℝ) : Fin e → ((Σ k, ι k) → ℂ) → ℝ :=
  fun j z =>
    if (j : ℕ) < 2 * k then u j 0 * Real.log (X₀.h z) + u j 1 * Real.log (X₁.h z) else Real.log (A₀.h z)

def wwLinProd (k : ℕ) (u : ℕ → Fin 2 → ℝ) : MvPolynomial (Fin 2) ℝ :=
  ∏ n ∈ Finset.range (2 * k), (C (u n 0) * X 0 + C (u n 1) * X 1)

def wwFibreMoment (w : S2 × S2 → ℝ) (Q : MvPolynomial (Fin 2) ℝ) : MvPolynomial (Fin 3) ℝ :=
  momentPoly (sphereMeasure.prod sphereMeasure) w
    (aeval ![dotPoly (Prod.fst : S2 × S2 → S2), dotPoly Prod.snd] (pderiv 0 (pderiv 1 Q)))

def wwLogWeight (p : S2 × S2) : ℝ :=
  (1 / 2 : ℝ) * Real.log ((1 - inner ℝ (p.1 : E3) (p.2 : E3)) / 2)

def WWFibrePoly.Statement : Prop :=
  ∀ (D : ℕ) (S : ProjectiveLineBundle D) (X A : HermLine S.YIdx) (X₀ X₁ A₀ : HermLine S.WIdx),
    S.IsXi X → IsSmoothHerm A → IsFromBase A → IsPullHerm (diagonalBlockIndex 0) (T.yyEmb 0) X X₀ →
    IsPullHerm (diagonalBlockIndex 1) (T.yyEmb 1) X X₁ → IsPullHerm (diagonalBlockIndex 0) (T.yyEmb 0) A A₀ →
    ∀ k : ℕ, 1 ≤ k → 2 * k ≤ D + 1 →
      ∃ Λ : MvPolynomial (Fin 3) ℝ →ₗ[ℝ] ℝ, ∀ u : ℕ → Fin 2 → ℝ,
        ptsIntegral S.WW (wwLinPot (e := D + 1) X₀ X₁ A₀ k u) (diagLogNorm S.g S.h X₀ X₁) =
            2 ^ (2 * k) * Λ (wwFibreMoment wwLogWeight (wwLinProd k u)) ∧
          ptsIntegral S.WW (wwLinPot (e := D + 1) X₀ X₁ A₀ k u) (fun _ => 1) =
            2 ^ (2 * k) * Λ (wwFibreMoment (fun _ => 1) (wwLinProd k u))

end

end GroundTheory.Heights₂.Heights.Inter
