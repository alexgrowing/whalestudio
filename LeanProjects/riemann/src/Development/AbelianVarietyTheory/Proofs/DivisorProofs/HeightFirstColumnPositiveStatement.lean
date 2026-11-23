import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightFirstColumnPositive
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
theorem _root_.GlobalTheory.T.height_first_column_positive : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (L : Submodule (𝓞 E) (Fin n → E))
    (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ), HidaSetting σ J X Y L a h →
      0 < GlobalTheory.EisMidHt.ht L a (GlobalTheory.EisMidHt.adVec F (GlobalTheory.EisMidHt.firstColumn X)) ∧
      ∀ g : GAd σ J, h g * GlobalTheory.EisMidHt.ht L a ((matHom _ σ J g⁻¹).1 *ᵥ GlobalTheory.EisMidHt.adVec F (GlobalTheory.EisMidHt.firstColumn X)) =
        GlobalTheory.EisMidHt.ht L a (GlobalTheory.EisMidHt.adVec F (GlobalTheory.EisMidHt.firstColumn X)) := by
  first | exact @GlobalTheory.EisMidHt.ht_iwasawa | exact GlobalTheory.EisMidHt.ht_iwasawa | (intros; apply GlobalTheory.EisMidHt.ht_iwasawa <;> assumption)
