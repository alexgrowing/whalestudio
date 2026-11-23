import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAutomorphicSideEmptyLocalStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsNbcAuSide
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nbc_auSide_true_of_isEmpty_loc : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7), IsEmpty D.nd.Loc → ∀ T : GlobalTheory.RowTie.WDTie D.nd D.naut, ∃ (C : NBC D.naut) (A : _root_.GlobalTheory.HeightCounting.AUSideAlt (setBC D C)), _root_.GlobalTheory.HeightCounting.AutomorphicSideRealised hL (setBC D C) T A := by
  first | exact @_root_.GlobalTheory.AutQuot.exists_nbc_auSide_auTrue_of_isEmpty | exact _root_.GlobalTheory.AutQuot.exists_nbc_auSide_auTrue_of_isEmpty | (intros; apply _root_.GlobalTheory.AutQuot.exists_nbc_auSide_auTrue_of_isEmpty <;> assumption)
end
