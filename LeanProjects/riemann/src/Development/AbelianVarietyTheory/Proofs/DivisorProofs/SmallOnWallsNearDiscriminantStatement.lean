import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallOnWallsNearDiscriminant
import Formalism.DegreeFormula.PointDegree.PowSum
import Formalism.DegreeFormula.PointDegree.PermExpInj
import Development.AbelianVarietyTheory.Definitions.Foundations.CurveCl
open MvPolynomial Formalism.DegreeFormula GlobalTheory.FlagPoly
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.small_on_walls_near_discriminant : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (j : ℕ), 1 ≤ j → j < N → ∃ C : ℝ, 0 < C ∧ ∀ (P : Pol ι N) (e : ℝ), 0 ≤ e → P.IsHomogeneous (dimFl ι N + 1) → AntiL j P → (∀ τ, ∀ lam ∈ wallSet (N := N) j τ (1 / (4 * (N : ℝ))), |ev lam P| ≤ e) → ∃ al be : ι → ℝ, CoefLe (P - delPol ι N * invForm j al be) (C * e) := by
  first | exact @GlobalTheory.FlagPoly.WallNear.near_discriminant_multiple | exact GlobalTheory.FlagPoly.WallNear.near_discriminant_multiple | (intros; apply GlobalTheory.FlagPoly.WallNear.near_discriminant_multiple <;> assumption)
