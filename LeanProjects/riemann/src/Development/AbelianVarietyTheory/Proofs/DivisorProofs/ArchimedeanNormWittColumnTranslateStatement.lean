import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanNormWittColumnTranslate
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreConcl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLineReps
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_norm_witt_column_translate : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (L : Submodule (𝓞 E) (Fin n → E))
    (a : GL (Fin n) (AF F ⊗[F] E)), IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y →
      GlobalTheory.EisLine.IsAdapted σ J X Y L a → ∀ y : Fin n → E, hE σ J (GlobalTheory.EisMidHt.firstColumn Y) y = 0 →
      ∀ (c : E) (w : InfinitePlace F),
        GlobalTheory.EisMidHt.normInf a w (fun i => compInf F E w (GlobalTheory.EisMidHt.adVec F (y + c • GlobalTheory.EisMidHt.firstColumn X) i)) =
          GlobalTheory.EisMidHt.normInf a w (fun i => compInf F E w (GlobalTheory.EisMidHt.adVec F y i)) +
            ‖Algebra.norm w.Completion (inclR (F := F) w.Completion c)‖ *
              GlobalTheory.EisMidHt.normInf a w (fun i => compInf F E w (GlobalTheory.EisMidHt.adVec F (GlobalTheory.EisMidHt.firstColumn X) i)) := by
  first | exact @GlobalTheory.ArchOrth.archimedean_norm_add_smul_first_column | exact GlobalTheory.ArchOrth.archimedean_norm_add_smul_first_column | (intros; apply GlobalTheory.ArchOrth.archimedean_norm_add_smul_first_column <;> assumption)
