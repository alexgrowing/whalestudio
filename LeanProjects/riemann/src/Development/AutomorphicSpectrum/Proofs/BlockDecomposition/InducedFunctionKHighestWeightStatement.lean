import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InducedFunctionKHighestWeight
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrderedCechToCatCochainsOneApplyValueAtSubset
open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inducedFunction_k_highest_weight : ∀ (n : ℕ) (lam : Fin n → ℤ), Antitone lam → ∀ lev : Fin n → ℕ, IsLev lam lev → ∀ F : GlobalTheory.CompanionTheory.ModelS.SmF n, F.1 = GlobalTheory.CompanionTheory.ModelS.fRaw lam lev → (∀ a b : Fin n, a < b → GlobalTheory.CompanionTheory.ModelS.Kf a b F = 0) ∧ ∀ a : Fin n, GlobalTheory.CompanionTheory.ModelS.Kf a a F = (GlobalTheory.CompanionTheory.ModelS.muZ lam lev a : ℂ) • F := by
  first | exact @GlobalTheory.CompanionTheory.ModelS.f_highest | exact GlobalTheory.CompanionTheory.ModelS.f_highest | (intros; apply GlobalTheory.CompanionTheory.ModelS.f_highest <;> assumption)
