import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchEmbeddingConjByAdelic
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arch_embedding_conj_by_adelic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (w : InfinitePlace F) (y : GArch σ J w) (b : GAd σ J),
      b⁻¹ * embArch σ J w y * b = embArch σ J w ((projArch σ J w b)⁻¹ * y * projArch σ J w b) := by
  first | exact @GlobalTheory.ConjArch.conj_embArch | exact GlobalTheory.ConjArch.conj_embArch | (intros; apply GlobalTheory.ConjArch.conj_embArch <;> assumption)
