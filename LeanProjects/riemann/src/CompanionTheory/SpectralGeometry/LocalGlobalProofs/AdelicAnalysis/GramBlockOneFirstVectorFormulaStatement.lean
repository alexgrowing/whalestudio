import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramBlockOneFirstVectorFormula
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.StageData
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gram_block_one_first_vector_formula : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] (u : R) (c : Fin n → R ⊗[F] E) (X : Fin n → Fin M → R ⊗[F] E), gramR R σ (blockOne (algebraMap F E t) J) (vec (u ⊗ₜ[F] (1 : E)) c X) 0 0 = (u ^ 2 * algebraMap F R t) ⊗ₜ[F] (1 : E) ∧ (∀ j : Fin n, gramR R σ (blockOne (algebraMap F E t) J) (vec (u ⊗ₜ[F] (1 : E)) c X) 0 j.succ = (u ⊗ₜ[F] (algebraMap F E t)) * c j) ∧ ∀ i j : Fin n, gramR R σ (blockOne (algebraMap F E t) J) (vec (u ⊗ₜ[F] (1 : E)) c X) i.succ j.succ = sigR R σ (c i) * inclR R (algebraMap F E t) * c j + gramR R σ J X i j := by
  first | exact @GlobalTheory.CompanionTheory.SW.PiLocalization₂.gramR_vec | exact GlobalTheory.CompanionTheory.SW.PiLocalization₂.gramR_vec | (intros; apply GlobalTheory.CompanionTheory.SW.PiLocalization₂.gramR_vec <;> assumption)
