import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralRightDerivativeEqZero
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrderedCechToCatCochainsOneApplyValueAtSubset
open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_right_derivative_eq_zero : ∀ (n : ℕ) [MeasurableSpace (Matrix.unitaryGroup (Fin n) ℂ)] [BorelSpace (Matrix.unitaryGroup (Fin n) ℂ)] (κ : Measure (Matrix.unitaryGroup (Fin n) ℂ)) [IsFiniteMeasure κ] [κ.IsMulRightInvariant] (u : Mat n → ℂ), ContDiffOn ℝ ∞ u (GLs n) → ∀ X : Mat n, Xᴴ = -X → ∫ k : Matrix.unitaryGroup (Fin n) ℂ, Rd X u k.1 ∂κ = 0 := by
  first | exact @GlobalTheory.CompanionTheory.ModelS.SkewInt.integral_Rd_skew | exact GlobalTheory.CompanionTheory.ModelS.SkewInt.integral_Rd_skew | (intros; apply GlobalTheory.CompanionTheory.ModelS.SkewInt.integral_Rd_skew <;> assumption)
