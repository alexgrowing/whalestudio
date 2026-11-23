import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothCholeskyFactor
import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.SymZeroCommFrame
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeMeas
open MeasureTheory Matrix Topology Filter
open scoped ContDiff ENNReal ComplexOrder Pointwise
open PositivityTheory.RgTw (Mat G hb)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.ConeHaar
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_positive_definite_sqrt : ∀ n : ℕ, ∃ σ₀ : Mat n → Mat n, ContDiffOn ℝ ∞ σ₀ {P | P.PosDef} ∧ ∀ P : Mat n, P.PosDef → σ₀ P * (σ₀ P)ᴴ = P := by
  first | exact @GlobalTheory.CompanionTheory.ConeHaar.Chol.exists_smooth_section | exact GlobalTheory.CompanionTheory.ConeHaar.Chol.exists_smooth_section | (intros; apply GlobalTheory.CompanionTheory.ConeHaar.Chol.exists_smooth_section <;> assumption)
