import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsPermShiftedWeightEqInfChar
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrderedCechToCatCochainsOneApplyValueAtSubset
open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_perm_shifted_weight_eq_inf_char : ∀ (n : ℕ) (lam : Fin n → ℤ) (lev : Fin n → ℕ), IsLev lam lev → ∃ σ : Equiv.Perm (Fin n), ∀ a : Fin n, (GlobalTheory.CompanionTheory.ModelS.yZ lam lev a : ℂ) + ((n : ℂ) - 1) / 2 - ((a : ℕ) : ℂ) = infOf lam false (σ a) := by
  first | exact @GlobalTheory.CompanionTheory.ModelS.ReversedBlocks.exists_perm_yZ | exact GlobalTheory.CompanionTheory.ModelS.ReversedBlocks.exists_perm_yZ | (intros; apply GlobalTheory.CompanionTheory.ModelS.ReversedBlocks.exists_perm_yZ <;> assumption)
