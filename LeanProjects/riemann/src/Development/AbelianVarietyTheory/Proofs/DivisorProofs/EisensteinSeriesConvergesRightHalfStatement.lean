import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinSeriesConvergesRightHalf
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreConcl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransv
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisenstein_series_converges_right_half : GlobalTheory.Published.EisensteinIsotropicLine → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (L : Submodule (𝓞 E) (Fin n → E))
    (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ), HidaSetting σ J X Y L a h →
    ∀ T, GlobalTheory.EisCT.IsTransv σ J (col0 X) T → ∀ s : ℝ, (n : ℝ) - 2 < s →
      ∑' t : GlobalTheory.EisCT.midSet σ J (col0 X) T, ENNReal.ofReal (h t.1.1 ^ s) < ⊤ := by
  first | exact @GlobalTheory.EisMidHt.midSet_sum_rpow_lt_top | exact GlobalTheory.EisMidHt.midSet_sum_rpow_lt_top | (intros; apply GlobalTheory.EisMidHt.midSet_sum_rpow_lt_top <;> assumption)
