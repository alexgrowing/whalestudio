import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InducedFunctionAtOne
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrderedCechToCatCochainsOneApplyValueAtSubset
open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inducedFunction_at_one : ∀ (n : ℕ) (lam : Fin n → ℤ) (lev : Fin n → ℕ), GlobalTheory.CompanionTheory.ModelS.fRaw lam lev 1 = 1 := by
  first | exact @GlobalTheory.CompanionTheory.ModelS.fRaw_one | exact GlobalTheory.CompanionTheory.ModelS.fRaw_one | (intros; apply GlobalTheory.CompanionTheory.ModelS.fRaw_one <;> assumption)
