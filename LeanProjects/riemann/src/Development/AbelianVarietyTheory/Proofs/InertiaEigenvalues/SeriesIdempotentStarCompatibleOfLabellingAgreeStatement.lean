import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SeriesIdempotentStarCompatibleOfLabellingAgree
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seriesIdempotentStarCompatible_of_labelling_agree : Green → ∀ (D : D7) (L : ∀ k, LabelDatum (D.host.g k)), LabTie D L → GlobalTheory.GoodTypes.SeriesConj D := by
  first | exact @GlobalTheory.GoodTypes.seriesConj_of_labTie | exact GlobalTheory.GoodTypes.seriesConj_of_labTie | (intros; apply GlobalTheory.GoodTypes.seriesConj_of_labTie <;> assumption)
