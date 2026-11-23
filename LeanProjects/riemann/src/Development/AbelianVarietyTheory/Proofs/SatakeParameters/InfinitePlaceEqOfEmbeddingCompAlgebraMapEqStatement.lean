import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InfinitePlaceEqOfEmbeddingCompAlgebraMapEq
import Mathlib
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.infinitePlace_eq_of_embedding_comp_algebraMap_eq' : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] [Algebra.IsQuadraticExtension F E] (w₁ w₂ : InfinitePlace E), w₁.embedding.comp (algebraMap F E) = w₂.embedding.comp (algebraMap F E) → w₁ = w₂ := by
  first | exact @GlobalTheory.infinitePlace_eq_of_embedding_comp_algebraMap_eq | exact GlobalTheory.infinitePlace_eq_of_embedding_comp_algebraMap_eq | (intros; apply GlobalTheory.infinitePlace_eq_of_embedding_comp_algebraMap_eq <;> assumption)
