import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KActionSkewAdjointL2
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrderedCechToCatCochainsOneApplyValueAtSubset
open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.k_action_skew_adjoint_l2 : ∀ (n : ℕ) [MeasurableSpace (Matrix.unitaryGroup (Fin n) ℂ)] [BorelSpace (Matrix.unitaryGroup (Fin n) ℂ)] (κ : Measure (Matrix.unitaryGroup (Fin n) ℂ)) [IsFiniteMeasure κ], (∀ u : Mat n → ℂ, ContDiffOn ℝ ∞ u (GLs n) → ∀ X : Mat n, Xᴴ = -X → ∫ k : Matrix.unitaryGroup (Fin n) ℂ, Rd X u k.1 ∂κ = 0) → ∀ (a b : Fin n) (x y : GlobalTheory.CompanionTheory.ModelS.SmF n), GlobalTheory.CompanionTheory.ModelS.ipK κ (GlobalTheory.CompanionTheory.ModelS.Kf a b x) y = GlobalTheory.CompanionTheory.ModelS.ipK κ x (GlobalTheory.CompanionTheory.ModelS.Kf b a y) := by
  first | exact @GlobalTheory.CompanionTheory.ModelS.ipK_Kf_transpose | exact GlobalTheory.CompanionTheory.ModelS.ipK_Kf_transpose | (intros; apply GlobalTheory.CompanionTheory.ModelS.ipK_Kf_transpose <;> assumption)
