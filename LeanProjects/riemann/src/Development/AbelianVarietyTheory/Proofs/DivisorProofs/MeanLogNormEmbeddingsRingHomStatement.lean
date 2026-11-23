import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeanLogNormEmbeddingsRingHom
import Mathlib
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mean_log_norm_embeddings_ringHom_eq : ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] (σ : 𝓞 E →+* 𝓞 K) (x : 𝓞 E),
  (∑ s : K →+* ℂ, Real.log ‖s (σ x : K)‖) / Module.finrank ℚ K =
    Real.log |((Algebra.norm ℚ (x : E) : ℚ) : ℝ)| / Module.finrank ℚ E := by
  first | exact @GlobalTheory.mean_log_norm_embeddings_ringHom | exact GlobalTheory.mean_log_norm_embeddings_ringHom | (intros; apply GlobalTheory.mean_log_norm_embeddings_ringHom <;> assumption)
