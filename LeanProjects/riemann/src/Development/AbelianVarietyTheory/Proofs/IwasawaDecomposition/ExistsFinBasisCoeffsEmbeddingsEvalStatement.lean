import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFinBasisCoeffsEmbeddingsEval
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finBasis_coeffs_embeddings_eval : ∀ (L : Type) [Field L] [NumberField L] (K : Type) [Field K] [CharZero K] (z : (L →+* K) → K), ∃ y : Fin (Module.finrank ℚ L) → K, ∀ σ : L →+* K, ∑ i, σ (Module.finBasis ℚ L i) * y i = z σ := by
  first | exact @GlobalTheory.embeddings_eval_onto | exact GlobalTheory.embeddings_eval_onto | (intros; apply GlobalTheory.embeddings_eval_onto <;> assumption)
