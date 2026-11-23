import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.BicommutantTensorFactorPermMemSpan
import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsLieDataCircle
open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bicommutant_tensorFactorPerm_mem_span : ∀ (n d : ℕ) (M : Matrix (Fin d → Fin n) (Fin d → Fin n) ℂ), (∀ T : Matrix (Fin d → Fin n) (Fin d → Fin n) ℂ, (∀ π, T * permMat n d π = permMat n d π * T) → M * T = T * M) → M ∈ Submodule.span ℂ (Set.range (permMat n d)) := by
  first | exact @GlobalTheory.SmoothForms.bicomm_permMat | exact GlobalTheory.SmoothForms.bicomm_permMat | (intros; apply GlobalTheory.SmoothForms.bicomm_permMat <;> assumption)
