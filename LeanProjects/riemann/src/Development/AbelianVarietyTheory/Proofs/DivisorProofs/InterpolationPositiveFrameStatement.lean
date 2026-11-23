import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InterpolationPositiveFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightBoundConst
open Matrix Filter Topology Set GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HermitianInterpolation GlobalTheory.InterpCurv
open scoped ComplexOrder ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.interpolation_positive_frame : ∀ {ι n : Type} [Fintype ι] [Fintype n] [DecidableEq n] {U : Set (ι → ℂ)} {H₀ H : (ι → ℂ) → Matrix n n ℂ} {s : (ι → ℂ) → ℝ}, IsPosFrame U H₀ → IsPosFrame U H → ContDiffOn ℝ ∞ s U → (∀ z ∈ U, s z ∈ Icc (0 : ℝ) 1) → IsPosFrame U (interp H₀ H s) := by
  first | exact @GlobalTheory.InterpPos.interp_isPosFrame | exact GlobalTheory.InterpPos.interp_isPosFrame | (intros; apply GlobalTheory.InterpPos.interp_isPosFrame <;> assumption)
