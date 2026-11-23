import Mathlib
import Formalism.GL3MeanSquares.SecondEstimateOfIntervalHypothesis

noncomputable section

namespace Formalism.HermitianLattices.ZeroDensityInBoxes

def ZeroDensityBox : Prop :=
  ∃ C : ℝ, ∀ (Q : ℝ) (S : Finset (Σ N : ℕ, DirichletCharacter ℂ (N + 1))), 3 ≤ Q →
    (∀ p ∈ S, p.2.IsPrimitive ∧ ((p.1 + 1 : ℕ) : ℝ) ≤ Q ∧
      ∃ s : ℂ, 1 - 1 / 400 < s.re ∧ |s.im| ≤ Q ∧ DirichletCharacter.LFunction p.2 s = 0) →
    (S.card : ℝ) ≤ C * Q ^ (1 / 4 : ℝ)

def BoxTailAll : Prop :=
  ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∃ C x₀ : ℝ, Formalism.HermitianLattices.ZeroFreeRegionGL2.BoxTailHyp ε C x₀

def BoxCountOfZD : Prop :=
  ZeroDensityBox → ∃ C : ℝ, Formalism.HermitianLattices.ZeroFreeRegionGL2.BoxCountHyp C

end Formalism.HermitianLattices.ZeroDensityInBoxes
