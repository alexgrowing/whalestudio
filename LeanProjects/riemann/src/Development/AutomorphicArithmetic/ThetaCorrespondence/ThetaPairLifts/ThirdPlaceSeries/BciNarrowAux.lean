import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.NarrowCondition
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RecT
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RecSatakeRecTStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspidalOfLocalLanglands
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.UnitaryOfLocalLanglands
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CGTrueT
import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.BaseChangeDefiniteOfCmDatumRecLaws

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
section Ud
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
open PositivityTheory.Rg.BcN
namespace UpperTheory.BaseChangeIdentities
attribute [local instance] GlobalTheory.CuspRep.host_isCMField
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
end UpperTheory.BaseChangeIdentities
end Ud
section Pr
open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.BasicNotions Formalism.MainNotions.N GlobalTheory.DefiniteBC
open PositivityTheory.Rg.BcN
namespace UpperTheory.BaseChangeIdentities
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N}
attribute [local instance] host_isCMField
section Frozen
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions
end Frozen
section Closing
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField
  IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem aux_of_cgTrue_of_auTrue (hA : AscComp) : DefiniteN → GlobalTheory.Published.GenericUnitaryDualGL → GlobalTheory.Published.StandardCosocleGL →
    ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut) (A : _root_.GlobalTheory.HeightCounting.AUSideAlt D),
      _root_.GlobalTheory.HeightCounting.CGTrueT hL D T → _root_.GlobalTheory.HeightCounting.AutomorphicSideRealised hL D T A → SphericalInertData.Conclusion1 D := by
  intro hNT hGU hSC hL D T A hCG hAU
  obtain ⟨hP, hS, hSat⟩ := _root_.GlobalTheory.T.recProd_recSpeh_recSatake hGU hSC hL D.nd D.naut T
  exact _root_.UpperTheory.One.M.Ud.baseChangeDefinite_of_cmDatum_recLaws D (_root_.GlobalTheory.FormDict.recT_alt T hL) hNT
    (discCsd_of hA D.host.E) hP hS hSat
    (_root_.GlobalTheory.T.cuspReadG_recT_of_cgTrue hL D T hCG) (_root_.GlobalTheory.T.unitary_of_local_langlands' hL D T A hAU)
end Closing
end UpperTheory.BaseChangeIdentities
end Pr
end
end
