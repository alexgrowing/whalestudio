import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WallSetCompactDominant
import Formalism.DegreeFormula.PointDegree.PowSum
import Formalism.DegreeFormula.PointDegree.PermExpInj
import Development.AbelianVarietyTheory.Definitions.Foundations.CurveCl
open MvPolynomial Formalism.DegreeFormula GlobalTheory.FlagPoly
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wall_set_compact_dominant : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (j : ℕ) (τ₀ : ι), 1 ≤ j → j < N → IsCompact (wallSet (N := N) j τ₀ (1 / (4 * (N : ℝ)))) ∧ (∀ lam ∈ wallSet (N := N) j τ₀ (1 / (4 * (N : ℝ))), Dom lam) ∧ ∃ U : Set (ι → Fin N → ℝ), IsOpen U ∧ (∃ x ∈ U, GapZero j τ₀ x) ∧ ∀ x ∈ U, GapZero j τ₀ x → x ∈ wallSet j τ₀ (1 / (4 * (N : ℝ))) := by
  first | exact @GlobalTheory.FlagPoly.wallSet_compact_dom_interior | exact GlobalTheory.FlagPoly.wallSet_compact_dom_interior | (intros; apply GlobalTheory.FlagPoly.wallSet_compact_dom_interior <;> assumption)
