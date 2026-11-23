import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PreimageDiagOneGeneralLinearEmbeddingIntegralGLS
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormMulApplyLeOne
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.preimage_diagOneGeneralLinearEmbedding_integralGLSet : ∀ (F : Type) [NormedField F] (r : ℕ), ⇑(GlobalTheory.JR.Step.emb r F) ⁻¹' glO (r + 1) F = glO r F := by
  first | exact @GlobalTheory.JR.GLift.emb_preimage_glO | exact GlobalTheory.JR.GLift.emb_preimage_glO | (intros; apply GlobalTheory.JR.GLift.emb_preimage_glO <;> assumption)
