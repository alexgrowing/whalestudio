import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JacquetShalikaExcludesRatioGap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDetProdConstAt
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability GlobalTheory.ThK.DetProd
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquet_shalika_excludes_ratio_gap : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (τ : GlobalTheory.CuspRep.CuspSub E 2)
    (w : HeightOneSpectrum (𝓞 E)) (ρ : GlobalTheory.CuspRep.SmIrr (GL (Fin 2) (w.adicCompletion E)))
    (χ₁ χ₂ : (w.adicCompletion E)ˣ →* ℂˣ), GlobalTheory.Published.JacquetShalikaBound → (GlobalTheory.CuspRep.CG.mk τ).IsUnitary →
    τ.IsLocComp w ρ → IsUnramAt w χ₁ → IsUnramAt w χ₂ → IsDetProdConstAt w 1 1 χ₁ χ₂ ρ.ρ → RatioGapAt w χ₁ χ₂ → False := by
  first | exact @GlobalTheory.ThK.DetProdSatake.false_of_ratioGap | exact GlobalTheory.ThK.DetProdSatake.false_of_ratioGap | (intros; apply GlobalTheory.ThK.DetProdSatake.false_of_ratioGap <;> assumption)
