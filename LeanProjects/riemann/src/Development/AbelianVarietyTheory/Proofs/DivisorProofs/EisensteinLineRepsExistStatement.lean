import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinLineRepsExist
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
theorem _root_.GlobalTheory.T.eisenstein_line_reps_exist : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (L : Submodule (𝓞 E) (Fin n → E))
    (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ), HidaSetting σ J X Y L a h →
      ∀ T, GlobalTheory.EisCT.IsTransv σ J (col0 X) T →
      ∃ Yr : Set (Fin n → E), GlobalTheory.EisMidHt.IsLineReps σ J (GlobalTheory.EisMidHt.firstColumn X) (GlobalTheory.EisMidHt.firstColumn Y) Yr ∧
        ∃ f : GlobalTheory.EisCT.midSet σ J (col0 X) T → Yr × E, Function.Injective f ∧
          ∀ t, ∃ μ : E, μ ≠ 0 ∧ (matHom _ σ J t.1.1⁻¹).1 *ᵥ GlobalTheory.EisMidHt.adVec F (GlobalTheory.EisMidHt.firstColumn X) =
            GlobalTheory.EisMidHt.adVec F (μ • ((f t).1.1 + (f t).2 • GlobalTheory.EisMidHt.firstColumn X)) := by
  first | exact @GlobalTheory.EisMidParam.midSet_param | exact GlobalTheory.EisMidParam.midSet_param | (intros; apply GlobalTheory.EisMidParam.midSet_param <;> assumption)
