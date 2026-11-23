import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosedDerivativeSystemSmooth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RwAppend
open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc GlobalTheory.CompanionTheory.PresSobA
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closed_derivative_system_smooth : ∀ (n : ℕ) (V P : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (o : P → Mat n → V) (d : (Bool × Fin n × Fin n) → P → P), (∀ v, ∀ z ∈ GLs n, DifferentiableAt ℝ (o v) z) → (∀ v p, ∀ z ∈ GLs n, Rd (bs p) (o v) z = o (d p v) z) → ∀ v, ContDiffOn ℝ ∞ (o v) (GLs n) := by
  first | exact @GlobalTheory.CompanionTheory.PresSobA.contDiffOn_of_right_family | exact GlobalTheory.CompanionTheory.PresSobA.contDiffOn_of_right_family | (intros; apply GlobalTheory.CompanionTheory.PresSobA.contDiffOn_of_right_family <;> assumption)
