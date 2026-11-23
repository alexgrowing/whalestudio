import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitIdeleAbsUniformizer
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBlockCentre
import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalFieldNormValuation
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability
open scoped TensorProduct
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_idele_abs_uniformizer : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (v : HeightOneSpectrum (𝓞 F)) (t : E →ₐ[F] Fv F v) (ϖ : (Fv F v)ˣ)
    (e : (Fv F v ⊗[F] E)ˣ), splitProj t (e : Fv F v ⊗[F] E) = ϖ → splitProj (t.comp σ) (e : Fv F v ⊗[F] E) = 1 →
    (GlobalTheory.Doubling.absE F E (GlobalTheory.Doubling.ideleAt F E v e) : ℝ) = nabs (Fv F v) ϖ := by
  first | exact @GlobalTheory.Div.IdeleAtNorm.absE_ideleAt_split | exact GlobalTheory.Div.IdeleAtNorm.absE_ideleAt_split | (intros; apply GlobalTheory.Div.IdeleAtNorm.absE_ideleAt_split <;> assumption)
