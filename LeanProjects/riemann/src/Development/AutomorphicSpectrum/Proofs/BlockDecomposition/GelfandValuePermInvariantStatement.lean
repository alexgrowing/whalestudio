import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GelfandValuePermInvariant
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrderedCechToCatCochainsOneApplyValueAtSubset
open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gelfand_value_perm_invariant : ∀ (n : ℕ) (χ : Fin n → ℂ) (σ : Equiv.Perm (Fin n)) (k : ℕ), GlobalTheory.Dec.gelfVal (fun a => χ (σ a)) k = GlobalTheory.Dec.gelfVal χ k := by
  first | exact @GlobalTheory.CompanionTheory.ModelS.gelfVal_perm | exact GlobalTheory.CompanionTheory.ModelS.gelfVal_perm | (intros; apply GlobalTheory.CompanionTheory.ModelS.gelfVal_perm <;> assumption)
