import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TotallyComplexSpanEmbeddingsAndFinrank
import Mathlib
open scoped Matrix
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.span_range_embedding_and_finrank_of_isTotallyComplex : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E], Submodule.span ℝ (Set.range (Pi.ringHom fun w : InfinitePlace E => w.embedding)) = ⊤ ∧ Module.finrank ℝ (InfinitePlace E → ℂ) = Module.finrank ℚ E := by
  first | exact @GlobalTheory.totallyComplex_span_embeddings_and_finrank | exact GlobalTheory.totallyComplex_span_embeddings_and_finrank | (intros; apply GlobalTheory.totallyComplex_span_embeddings_and_finrank <;> assumption)
