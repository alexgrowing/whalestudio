import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CutoffInterpolationAgreesFar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightBoundConst
open Matrix Filter Topology Set GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HermitianInterpolation GlobalTheory.InterpCurv
open scoped ComplexOrder ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cutoff_interpolation_agrees_far : ∀ {ι n : Type} [Fintype ι] [Fintype n] [DecidableEq n] {χ : ℝ → ℝ}, IsCutoff χ → ∀ {κ t R : ℝ}, 2 ≤ R → ∀ {U : Set (ι → ℂ)} {H₀ H : (ι → ℂ) → Matrix n n ℂ} {r : (ι → ℂ) → ℝ}, (∀ z ∈ U, Real.exp 1 ≤ r z) → IsPosFrame U (interp H₀ H fun x => t * cutWeight χ κ R r x) → (∀ z ∈ U, R ^ 3 ≤ r z → interp H₀ H (fun x => t * cutWeight χ κ R r x) z = H₀ z) ∧ ∀ V : Set (ι → ℂ), U ⊆ V → IsPosFrame V H₀ → (∀ z ∈ V \ U, Tendsto r (𝓝[U] z) atTop) → IsPosFrame V fun z => open Classical in if z ∈ U then interp H₀ H (fun x => t * cutWeight χ κ R r x) z else H₀ z := by
  first | exact @GlobalTheory.InterpCurv.interp_cutWeight_eq_and_glue | exact GlobalTheory.InterpCurv.interp_cutWeight_eq_and_glue | (intros; apply GlobalTheory.InterpCurv.interp_cutWeight_eq_and_glue <;> assumption)
