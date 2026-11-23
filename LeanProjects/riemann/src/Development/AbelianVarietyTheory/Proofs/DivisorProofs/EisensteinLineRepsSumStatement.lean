import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinLineRepsSum
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
theorem _root_.GlobalTheory.T.eisenstein_line_reps_sum : GlobalTheory.Published.EisensteinIsotropicLine → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (L : Submodule (𝓞 E) (Fin n → E))
    (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ), HidaSetting σ J X Y L a h →
      ∀ Yr : Set (Fin n → E), GlobalTheory.EisMidHt.IsLineReps σ J (GlobalTheory.EisMidHt.firstColumn X) (GlobalTheory.EisMidHt.firstColumn Y) Yr →
      ∀ s : ℝ, (n : ℝ) - 3 < s → ∑' y : Yr, ENNReal.ofReal (GlobalTheory.EisMidHt.ht L a (GlobalTheory.EisMidHt.adVec F y.1) ^ (-s)) < ⊤ := by
  first | exact @GlobalTheory.EisMidHt.midLines_sum_rpow_lt_top | exact GlobalTheory.EisMidHt.midLines_sum_rpow_lt_top | (intros; apply GlobalTheory.EisMidHt.midLines_sum_rpow_lt_top <;> assumption)
