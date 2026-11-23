import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousUnitaryDiagonalEmbeddingDoubled
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReindexDblIncM
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeltaTApply
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_continuous_unitaryDiagonalEmbedding_doubled : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n : ℕ) (J : Matrix (Fin n) (Fin n) E),
      ∃ ι : Formalism.IndefR.DatumF.GAF σ J →* Formalism.IndefR.DatumF.GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG J),
        Continuous ι ∧
        (∀ h, Formalism.IndefR.DatumF.mtF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG J) (ι h) =
          Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks (Formalism.IndefR.DatumF.mtF σ J h) 0 0 1)) ∧
        (∀ γ ∈ Formalism.IndefR.DatumF.GQF σ J, ι γ ∈ Formalism.IndefR.DatumF.GQF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG J)) ∧
        (∀ e h, Formalism.IndefR.DatumF.SuppAtF σ e J h → Formalism.IndefR.DatumF.SuppAtF σ e (GlobalTheory.WeilSchrodinger.DblTargetF.dblG J) (ι h)) ∧
        (∀ e h y, Formalism.IndefR.DatumF.IsDetAtF σ e J h y →
          Formalism.IndefR.DatumF.IsDetAtF σ e (GlobalTheory.WeilSchrodinger.DblTargetF.dblG J) (ι h) y) := by
  first | exact @GlobalTheory.DiagEmbU.exists_diagEmb | exact GlobalTheory.DiagEmbU.exists_diagEmb | (intros; apply GlobalTheory.DiagEmbU.exists_diagEmb <;> assumption)
