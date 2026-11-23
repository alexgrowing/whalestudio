import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RightDerivativeRealLieHom
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrderedCechToCatCochainsOneApplyValueAtSubset
open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.right_derivative_real_lie_hom : ∀ (n : ℕ), (∀ X Y : Mat n, GlobalTheory.CompanionTheory.ModelS.DR (X + Y) = GlobalTheory.CompanionTheory.ModelS.DR X + GlobalTheory.CompanionTheory.ModelS.DR Y) ∧ (∀ (r : ℝ) (X : Mat n), GlobalTheory.CompanionTheory.ModelS.DR ((r : ℂ) • X) = (r : ℂ) • GlobalTheory.CompanionTheory.ModelS.DR X) ∧ (∀ X Y : Mat n, GlobalTheory.CompanionTheory.ModelS.DR (X * Y - Y * X) = GlobalTheory.CompanionTheory.ModelS.DR X * GlobalTheory.CompanionTheory.ModelS.DR Y - GlobalTheory.CompanionTheory.ModelS.DR Y * GlobalTheory.CompanionTheory.ModelS.DR X) := by
  first | exact @GlobalTheory.CompanionTheory.ModelS.LieAct.DR_lie | exact GlobalTheory.CompanionTheory.ModelS.LieAct.DR_lie | (intros; apply GlobalTheory.CompanionTheory.ModelS.LieAct.DR_lie <;> assumption)
