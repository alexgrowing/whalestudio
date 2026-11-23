import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinSeriesFunctionalBound
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
theorem _root_.GlobalTheory.T.eisenstein_eq_lineSum_add_midSum_add_bigSum : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (L : Submodule (𝓞 E) (Fin n → E))
    (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ) (Eis : ℂ → GAd σ J → ℂ), HidaSetting σ J X Y L a h → IsSerG σ J (col0 X) h Eis →
    ∀ T, GlobalTheory.EisCT.IsTransv σ J (col0 X) T → ∀ s : ℂ, ((n : ℝ) - 1) / 2 < s.re → ∀ g,
    Eis s g = GlobalTheory.EisCT.lineSum σ J (col0 X) T h s g + GlobalTheory.EisCT.midSum σ J (col0 X) T h s g +
      GlobalTheory.EisCT.bigSum σ J (col0 X) T h s g := by
  first | exact @GlobalTheory.EisCT.eis_eq_three_sums | exact GlobalTheory.EisCT.eis_eq_three_sums | (intros; apply GlobalTheory.EisCT.eis_eq_three_sums <;> assumption)
