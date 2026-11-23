import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExponentEstimateFromLanglandsStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WeightsConj
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExportSt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExpStOfStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NumSt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SumExpStStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ModelStOfFramesStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SmallStStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FrameStOfSmallStStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GaloisAtPlaceOfAutomorphicAtPlace
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
section
set_option autoImplicit false
namespace GlobalTheory.BigOn
theorem exponent_bound_of_unitaryThetaStandardTheorems_alt :
    GlobalTheory.Published.ClozelCohomological →
      GlobalTheory.Published.HeckeLAdicCharacter →
      GlobalTheory.Published.ChebotarevDegreeOne →
      _root_.UpperTheory.GalS.CuspUAlt →
      _root_.GlobalTheory.Published.BaseChangeDefiniteUnitaryGroup →
      GlobalTheory.Published.BhattScholzeCrystallineLattices →
      GlobalTheory.Published.HeckeLAdicCharacterAbove →
      _root_.UpperTheory.Zero.LLC.RecTExists →
      _root_.GlobalTheory.BigOn.ExponentStatement :=
  fun hCoh hHecke hCheb hGal hBC hBS hAbove hLL =>
    _root_.GlobalTheory.T.expSt_of_num_sumExp_model GlobalTheory.T.weylLattice_exact_exponent_block_cut _root_.GlobalTheory.ExpTie.numSt_alt _root_.GlobalTheory.T.sum_expansion'
      (_root_.GlobalTheory.T.model_statement_of_crystalline_chebotarev_frame_gal hBS hCheb _root_.GlobalTheory.T.small_estimate (_root_.GlobalTheory.T.frame_statement_of_small_statement _root_.GlobalTheory.T.small_estimate)
        (_root_.GlobalTheory.T.galois_frame_compatibility_alt hCoh hHecke hCheb hGal hBC hBS hAbove hLL _root_.GlobalTheory.T.small_estimate))
end GlobalTheory.BigOn
end
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.expSt_of_base_change_and_crystalline_lattices : GlobalTheory.Published.ClozelCohomological → GlobalTheory.Published.HeckeLAdicCharacter → GlobalTheory.Published.ChebotarevDegreeOne → _root_.UpperTheory.GalS.CuspUAlt → _root_.GlobalTheory.Published.BaseChangeDefiniteUnitaryGroup → GlobalTheory.Published.BhattScholzeCrystallineLattices → GlobalTheory.Published.HeckeLAdicCharacterAbove → _root_.UpperTheory.Zero.LLC.RecTExists → _root_.GlobalTheory.BigOn.ExponentStatement := by
  first | exact @_root_.GlobalTheory.BigOn.exponent_bound_of_unitaryThetaStandardTheorems_alt | exact _root_.GlobalTheory.BigOn.exponent_bound_of_unitaryThetaStandardTheorems_alt | (intros; apply _root_.GlobalTheory.BigOn.exponent_bound_of_unitaryThetaStandardTheorems_alt <;> assumption)
end
end
