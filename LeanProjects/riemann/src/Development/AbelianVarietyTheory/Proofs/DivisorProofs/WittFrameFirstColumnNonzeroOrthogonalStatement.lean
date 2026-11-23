import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittFrameFirstColumnNonzeroOrthogonal
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
theorem _root_.GlobalTheory.T.witt_frame_first_column_nonzero_orthogonal : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (L : Submodule (𝓞 E) (Fin n → E))
    (a : GL (Fin n) (AF F ⊗[F] E)), IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y →
      GlobalTheory.EisLine.IsAdapted σ J X Y L a →
      GlobalTheory.EisMidHt.firstColumn X ≠ 0 ∧
      ∀ y : Fin n → E, hE σ J (GlobalTheory.EisMidHt.firstColumn X) y = 0 → hE σ J (GlobalTheory.EisMidHt.firstColumn Y) y = 0 →
        (∀ c : E, y ≠ 0 → y + c • GlobalTheory.EisMidHt.firstColumn X ≠ 0) ∧
        ∀ c l : E, (l • (y + c • GlobalTheory.EisMidHt.firstColumn X) ∈ L ↔ l • y ∈ L ∧ (l * c) • GlobalTheory.EisMidHt.firstColumn X ∈ L) := by
  first | exact @GlobalTheory.AdaptedSplit.smul_add_mem_iff | exact GlobalTheory.AdaptedSplit.smul_add_mem_iff | (intros; apply GlobalTheory.AdaptedSplit.smul_add_mem_iff <;> assumption)
