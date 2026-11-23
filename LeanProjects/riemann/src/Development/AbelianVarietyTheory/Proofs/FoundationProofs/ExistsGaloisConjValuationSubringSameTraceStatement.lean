import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsGaloisConjValuationSubringSameTrace
import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiagMod
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_galois_conj_valuationSubring_same_trace : ∀ (F L : Type) [Field F] [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L] (W₁ W₂ : ValuationSubring L), (∀ a : F, algebraMap F L a ∈ W₁ ↔ algebraMap F L a ∈ W₂) → ∃ σ : L ≃ₐ[F] L, ∀ x : L, σ x ∈ W₂ ↔ x ∈ W₁ := by
  first | exact @GlobalTheory.KZ.ES.exists_conj_of_same_trace | exact GlobalTheory.KZ.ES.exists_conj_of_same_trace | (intros; apply GlobalTheory.KZ.ES.exists_conj_of_same_trace <;> assumption)
