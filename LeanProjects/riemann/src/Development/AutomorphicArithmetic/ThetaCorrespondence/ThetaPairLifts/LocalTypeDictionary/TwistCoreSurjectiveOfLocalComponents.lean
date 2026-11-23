import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaSurjectiveDefiniteLevel
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistEvenSurjectiveOfRepresentatives
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.SeparatingFamilyHasModels
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaSurjectiveDefiniteLevelStatement

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Twist.CoreOntoAssembly
theorem twist_core_surjective_of_local_components : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Hk3.HoweUnram → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelWeilUnitaryConvergent → _root_.GlobalTheory.Published.DoublingMethodLocalZetaIntegrals → GlobalTheory.Published.UnramifiedDoublingGL → CoreOnto := by
  intro hP hHCF hCRD hDSC hHCM hCW hHowe hWeil hWSF hSWC hDbl hUDG
  exact GlobalTheory.T.coreChain_lifts_surjective_of_evenRank
    (_root_.GlobalTheory.T.twist_even_surjective_of_representatives hHCF hCRD hDSC hHCM hCW hHowe hWeil hWSF hSWC hDbl hUDG)
    GlobalTheory.T.testGridCommonData_properties_hold GlobalTheory.T.testGridStageLatticesProperties_proof
    (GlobalTheory.T.core_chain_composites_exist_lift_combinations hDSC hHCM hCRD hCW GlobalTheory.T.dependence_fixed (_root_.GlobalTheory.T.exists_separating_models hP))
    GlobalTheory.T.definiteTopSpace_columnValues
end GlobalTheory.Twist.CoreOntoAssembly
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_core_surjective : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Hk3.HoweUnram → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelWeilUnitaryConvergent → _root_.GlobalTheory.Published.DoublingMethodLocalZetaIntegrals → GlobalTheory.Published.UnramifiedDoublingGL → CoreOnto := by
  first | exact @_root_.GlobalTheory.Twist.CoreOntoAssembly.twist_core_surjective_of_local_components | exact _root_.GlobalTheory.Twist.CoreOntoAssembly.twist_core_surjective_of_local_components | (intros; apply _root_.GlobalTheory.Twist.CoreOntoAssembly.twist_core_surjective_of_local_components <;> assumption)
end
