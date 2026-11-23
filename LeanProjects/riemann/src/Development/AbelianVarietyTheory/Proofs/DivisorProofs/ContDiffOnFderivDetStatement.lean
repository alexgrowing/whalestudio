import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffOnFderivDet
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousAndSmul
open Filter Topology Set Metric MeasureTheory GlobalTheory.ChernReg
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contDiffOn_fderiv_det : ∀ (d : ℕ) (N : Set ((Fin d → ℂ) × (Fin d → ℂ))) (G : (Fin d → ℂ) × (Fin d → ℂ) → Fin d → ℂ), IsOpen N → ContDiffOn ℝ ∞ G N → ContDiffOn ℝ ∞ (fun p : (Fin d → ℂ) × (Fin d → ℂ) => (fderiv ℝ (fun ξ => G (p.1, ξ)) p.2).det) N := by
  first | exact @GlobalTheory.PartialDetSmooth.partialDet_contDiffOn | exact GlobalTheory.PartialDetSmooth.partialDet_contDiffOn | (intros; apply GlobalTheory.PartialDetSmooth.partialDet_contDiffOn <;> assumption)
