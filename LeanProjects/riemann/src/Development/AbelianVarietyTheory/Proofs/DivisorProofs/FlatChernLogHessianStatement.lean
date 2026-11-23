import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatChernLogHessian
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarEqZeroOfHolomorphic
open Matrix GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm GlobalTheory.TorsionForm.FlatAcyc
open scoped Real ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_chern_log_hessian : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g : ℕ} {B : Set E}
    {τ : E → Matrix (Fin g) (Fin g) ℂ} {h : Pt E g → ℝ} (hτ : IsPeriodMap B τ)
    (hh : ContDiffOn ℝ ∞ h (cov B g)) (hpos : ∀ P ∈ cov B g, 0 < h P) (hc : ChernIsFlat B τ h)
    {b : E} (hb : b ∈ B) (z : Fin g → ℂ) (a c : Fin g),
    d10 (fun z' => d01 (fun z'' => (Real.log (h (b, z'')) : ℂ)) z' (ev c)) z (ev a) =
      -(π : ℂ) * (imPart τ b)⁻¹ a c := by
  first | exact @GlobalTheory.FlatHessian.dholo_dbar_log_metric | exact GlobalTheory.FlatHessian.dholo_dbar_log_metric | (intros; apply GlobalTheory.FlatHessian.dholo_dbar_log_metric <;> assumption)
