import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RightDerivativeLowerBlockAtOne
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrderedCechToCatCochainsOneApplyValueAtSubset
open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.right_derivative_lower_block_at_one : ∀ (n : ℕ) (lev : Fin n → ℕ) (f h : GlobalTheory.CompanionTheory.ModelS.SmF n), f ∈ GlobalTheory.CompanionTheory.ModelS.Eqv lev f.1 → f.1 1 = 1 → h ∈ GlobalTheory.CompanionTheory.ModelS.Eqv lev f.1 → ∀ X : Mat n, (∀ a b, lev a < lev b → X a b = 0) → (GlobalTheory.CompanionTheory.ModelS.DR X h).1 1 = (GlobalTheory.CompanionTheory.ModelS.DR X f).1 1 * h.1 1 := by
  first | exact @GlobalTheory.CompanionTheory.ModelS.DR_one_of_eqv | exact GlobalTheory.CompanionTheory.ModelS.DR_one_of_eqv | (intros; apply GlobalTheory.CompanionTheory.ModelS.DR_one_of_eqv <;> assumption)
