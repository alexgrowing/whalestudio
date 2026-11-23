import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaParabolicUnitary
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrderedCechToCatCochainsOneApplyValueAtSubset
open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iwasawa_parabolic_unitary : ∀ (n : ℕ) (lev : Fin n → ℕ), Monotone lev → ∀ g ∈ GLs n, ∃ p ∈ GlobalTheory.CompanionTheory.ModelS.Pb lev, ∃ k : Matrix.unitaryGroup (Fin n) ℂ, g = p * k.1 := by
  first | exact @GlobalTheory.CompanionTheory.ModelS.exists_Pb_mul_unitary | exact GlobalTheory.CompanionTheory.ModelS.exists_Pb_mul_unitary | (intros; apply GlobalTheory.CompanionTheory.ModelS.exists_Pb_mul_unitary <;> assumption)
