import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

def NoCommonZeroComplex.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ι → ℕ) (P : ArithVariety n) (a : ι → ℤ)
    (J : Type) [Fintype J] (s : J → IntegralSection P a),
    (∀ x ∈ P.points (AlgebraicClosure ℚ), ∃ j, (s j).NonzeroAt x) →
    ∀ z ∈ P.points ℂ, ∃ (j : J) (c : (k : ι) → Fin (n k + 1)) (d : ι → ℕ)
      (e : MvPolynomial (Coord n) ℤ),
      IsChartForm P a (s j).num (s j).den c d e ∧ (∀ k, z k (c k) ≠ 0) ∧ evalCone z e ≠ 0

end GroundTheory.Heights₂.Heights
