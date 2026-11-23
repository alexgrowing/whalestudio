import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaussExtensionUniqueOfGauss
import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiagMod
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gauss_valuationSubring_unique_away_finset : ∀ {F : Type} [Field F] [CharZero F] [IsAlgClosed F] [Algebra.IsAlgebraic ℚ F] {L : Type} [Field L] [Algebra F L] (t : L), Transcendental F t → FiniteDimensional (IntermediateField.adjoin F {t}) L → ∃ S : Finset ℕ, ∀ q : ℕ, q.Prime → q ∉ S → ∀ V : ValuationSubring F, ((q : ℕ) : F) ∈ V.nonunits → ∀ W₁ W₂ : ValuationSubring L, Gauss t V W₁ → Gauss t V W₂ → W₁ = W₂ := by
  first | exact @GlobalTheory.BertiniNoether.gauss_extension_unique_of_gauss | exact GlobalTheory.BertiniNoether.gauss_extension_unique_of_gauss | (intros; apply GlobalTheory.BertiniNoether.gauss_extension_unique_of_gauss <;> assumption)
