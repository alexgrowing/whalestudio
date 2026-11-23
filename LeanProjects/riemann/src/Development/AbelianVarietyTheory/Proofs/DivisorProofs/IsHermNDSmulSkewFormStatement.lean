import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHermNDSmulSkewForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isHermND_smul_skew_form : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n : ℕ) (W : Spc F E n) (r s : ℕ), W.IsSkew σ B r s → ∀ c : E, c ≠ 0 → σ c = -c →
    IsHermND σ (c • W.J.map σ) := by
  first | exact @GlobalTheory.ThK.SqIntHerm.isHermND_smul_map | exact GlobalTheory.ThK.SqIntHerm.isHermND_smul_map | (intros; apply GlobalTheory.ThK.SqIntHerm.isHermND_smul_map <;> assumption)
