import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InducedFunctionDerivativeAtOne
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrderedCechToCatCochainsOneApplyValueAtSubset
open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inducedFunction_derivative_at_one : ∀ (n : ℕ) (lam : Fin n → ℤ), Antitone lam → ∀ lev : Fin n → ℕ, IsLev lam lev → ∀ F : GlobalTheory.CompanionTheory.ModelS.SmF n, F.1 = GlobalTheory.CompanionTheory.ModelS.fRaw lam lev → ∀ a b : Fin n, lev b ≤ lev a → (e1 GlobalTheory.CompanionTheory.ModelS.DR a b F).1 1 = (if a = b then (lam a : ℂ) else 0) ∧ (f1 GlobalTheory.CompanionTheory.ModelS.DR a b F).1 1 = (if a = b then (GlobalTheory.CompanionTheory.ModelS.yZ lam lev a : ℂ) else 0) := by
  first | exact @GlobalTheory.CompanionTheory.ModelS.FDer.fder | exact GlobalTheory.CompanionTheory.ModelS.FDer.fder | (intros; apply GlobalTheory.CompanionTheory.ModelS.FDer.fder <;> assumption)
