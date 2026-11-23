import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OntoXAndLamLowOfPublishedUE
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExportSt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Realised
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.OntoXOfPrints
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LlOf
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocalRepresentationTheoryHypotheses
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LamLowOfPublished

set_option synthInstance.maxHeartbeats 200000

section
section
namespace GlobalTheory.Fc.S0
theorem ontoX_and_lamLow_of_unitaryGroupHypotheses' :
    _root_.GlobalTheory.Fc.S0.UnitaryGroupThirdPlaceHypotheses → _root_.GlobalTheory.BigOn.SurjectiveOntoX ∧ _root_.GlobalTheory.BigTop.LambdaLowerBound₂ := by
  intro P
  exact ⟨_root_.GlobalTheory.BigOn.ontoX_of_hypotheses_alt_alt P.greenCuspidal P.clozelCohomological
      P.heckeLAdicCharacter P.chebotarevDegreeOne
      P.galoisRepOfPolarizedCuspidal P.baseChangeDefiniteUnitary
      P.bhattScholzeCrystallineLattices P.heckeLAdicCharacterAbove P.cuspRapidDecay
      (_root_.UpperTheory.One.M.New.llOf_alt P.litN.loc.llc P.litN.loc.conv
      P.litN.loc.dzi P.litN.loc.brauer P.litN.loc.chev P.globalArtinReciprocity P.litN.loc.exh
      P.litN.loc.multi P.litN.loc.cos P.litN.loc.zel P.litN.loc.geo P.litN.loc.bz)
      P.discreteSeriesCover P.casselmanWallach,
    _root_.GlobalTheory.BigTop.lamLow_of_hypotheses_alt_alt P.cuspRapidDecay P.weilSiegelFormulaUnitary
      P.siegelWeilUnitaryConvergent P.doublingMethod P.unramifiedDoublingGL
      P.bernsteinZelevinskyFiniteness P.formalDegreeCompactDual⟩
end GlobalTheory.Fc.S0
end
end
