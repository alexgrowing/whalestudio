import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalInverseFstProd
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousAndSmul
open Filter Topology Set Metric MeasureTheory GlobalTheory.ChernReg
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_inverse_fst_prod : ∀ (d : ℕ) (N : Set ((Fin d → ℂ) × (Fin d → ℂ))) (G : (Fin d → ℂ) × (Fin d → ℂ) → Fin d → ℂ) (z₀ : Fin d → ℂ), IsOpen N → (z₀, 0) ∈ N → ContDiffOn ℝ ∞ G N → HasFDerivAt (fun ξ => G (z₀, ξ)) (ContinuousLinearMap.id ℝ (Fin d → ℂ)) 0 → ∃ e : OpenPartialHomeomorph ((Fin d → ℂ) × (Fin d → ℂ)) ((Fin d → ℂ) × (Fin d → ℂ)), (z₀, 0) ∈ e.source ∧ e.source ⊆ N ∧ (∀ p ∈ e.source, e p = (p.1, G p)) ∧ ContDiffOn ℝ ∞ e.symm e.target ∧ ∀ p ∈ e.source, (fderiv ℝ (fun ξ => G (p.1, ξ)) p.2).det ≠ 0 := by
  first | exact @GlobalTheory.localInverse_fst_prod | exact GlobalTheory.localInverse_fst_prod | (intros; apply GlobalTheory.localInverse_fst_prod <;> assumption)
