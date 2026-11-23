import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InterpolatedConnectionDifference
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightBoundConst
open Matrix Filter Topology Set GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HermitianInterpolation GlobalTheory.InterpCurv
open scoped ComplexOrder ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.interpolated_connection_difference : ∀ {ι n : Type} [Fintype ι] [Fintype n] [DecidableEq n] {H₀ H : (ι → ℂ) → Matrix n n ℂ} {s : (ι → ℂ) → ℝ} {z : ι → ℂ}, MContDiffAt 1 H₀ z → MContDiffAt 1 H z → DifferentiableAt ℝ s z → IsUnit (H₀ z).det → IsUnit (H z).det → IsUnit (interp H₀ H s z).det → ∀ (ξ : ι → ℂ) (v w : n → ℂ), form (interp H₀ H s z) ((conn (interp H₀ H s) z ξ - conn H₀ z ξ) *ᵥ v) w = (s z : ℂ) * form (H z) ((conn H z ξ - conn H₀ z ξ) *ᵥ v) w + GlobalTheory.del (fun x => (s x : ℂ)) z ξ * (form (H z) v w - form (H₀ z) v w) := by
  first | exact @GlobalTheory.InterpDiff.form_conn_interp_sub | exact GlobalTheory.InterpDiff.form_conn_interp_sub | (intros; apply GlobalTheory.InterpDiff.form_conn_interp_sub <;> assumption)
