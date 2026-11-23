import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneParameterSkewHermitian
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.one_parameter_skew_hermitian : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (w : InfinitePlace F) (τ : EmbOver E w)
    (Z : Matrix (Fin n) (Fin n) ℂ) (y : ℝ → GArch σ J w),
    (∀ t : ℝ, GlobalTheory.Orb.archMat σ J τ (y t) = NormedSpace.exp (t • Z)) →
    Z.conjTranspose * J.map τ.1 + J.map τ.1 * Z = 0 := by
  first | exact @GlobalTheory.ThK.OneParamLie.lie_of_archMat_eq_exp | exact GlobalTheory.ThK.OneParamLie.lie_of_archMat_eq_exp | (intros; apply GlobalTheory.ThK.OneParamLie.lie_of_archMat_eq_exp <;> assumption)
