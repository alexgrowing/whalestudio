import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InterpolatedMetricPositive
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightBoundConst
open Matrix Filter Topology Set GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HermitianInterpolation GlobalTheory.InterpCurv
open scoped ComplexOrder ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.interpolated_metric_positive : ∀ {ι n : Type} [Fintype ι] [Fintype n] [DecidableEq n] {Cμ : ℝ} {U : Set (ι → ℂ)} {H₀ H : (ι → ℂ) → Matrix n n ℂ} {r s : (ι → ℂ) → ℝ}, IsPosFrame U H₀ → IsPosFrame U H → (∀ z ∈ U, Real.exp 1 ≤ r z) → ContDiffOn ℝ ∞ s U → (∀ z ∈ U, s z ∈ Icc (0 : ℝ) 1) → PowComparable U r Cμ H₀ H → IsPosFrame U (interp H₀ H s) ∧ PowComparable U r Cμ H₀ (interp H₀ H s) ∧ ∀ (σ : Type) (blk : n → σ), IsBlockDiag blk U H₀ → IsBlockDiag blk U H → IsBlockDiag blk U (interp H₀ H s) := by
  first | exact @GlobalTheory.InterpConvex.interp_isPosFrame_comparable_blockDiag | exact GlobalTheory.InterpConvex.interp_isPosFrame_comparable_blockDiag | (intros; apply GlobalTheory.InterpConvex.interp_isPosFrame_comparable_blockDiag <;> assumption)
