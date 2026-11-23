import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ModularityOfHyps
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.CuspOfPair
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
theorem UpperTheory.Lit.heckeLAdicCharacterCrystalline_of_deRham (h1 : GlobalTheory.Published.HeckeLAdicCharacterDeRham) (h2 : GlobalTheory.Published.DeRhamPotSemistable)
    (h3 : GlobalTheory.Published.AlgebraicCharacterWD) (h4 : _root_.UpperTheory.Zero.LLC.RecTExists) : GlobalTheory.Published.HeckeLAdicCharacterCrystalline :=
  _root_.GlobalTheory.Published.CharCrysModel.of_hypotheses_m_alt h1 h2 h3 h4
end
