import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExportStatementOfDiscreteSeries
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExportSt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowAtOfRatStep
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwAdmStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwChrOfTwAdmStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowAtOfStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LowAtHoldsStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CanExHoldsStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CanProjStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TieRatOfStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RecSideOfTwAdmStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AdaptExStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ConjBaseOfStepsStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwOneOfStepsStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsSeriesStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BaseGeOfStepsStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwLeStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwGeStatement

set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
namespace GlobalTheory.BigOn.Exp
theorem exportSt_of_hypotheses_alt (hC : GlobalTheory.Published.CuspRapidDecay) (hA : GlobalTheory.Published.GlobalArtinReciprocity)
    (hR : GlobalTheory.Published.RayClassFieldSt) (hD : GlobalTheory.Published.DiscreteSeriesCover) (hW : GlobalTheory.Published.CasselmanWallach)
    (hS : GlobalTheory.SerStd.SeriesRatS) : _root_.GlobalTheory.BigOn.ExportedStatement :=
  have tA := _root_.GlobalTheory.T.twist_admissible'
  have tC := _root_.GlobalTheory.T.twist_character_of_artin' hA tA
  have row := _root_.GlobalTheory.T.at_statement_of_low_weight_twAdm hC hA hR hS _root_.GlobalTheory.T.lowAt tA
  _root_.GlobalTheory.BigOn.Exp.InductionConditions.exportSt ⟨_root_.GlobalTheory.T.bigOn_canEx, _root_.GlobalTheory.T.bigOn_canProj, tA, row, _root_.GlobalTheory.T.tieRat_of_twAdm_and_at tA row, _root_.GlobalTheory.T.reciprocity_side_of_twAdm tA, _root_.GlobalTheory.T.adaptEx',
    _root_.GlobalTheory.T.conjBase_of_ray_class_field_and_seriesRat hC hA hR hS, _root_.GlobalTheory.T.conjTw_of_discrete_series_and_casselman_wallach hC hA hR hD hW hS tA tC, _root_.GlobalTheory.T.baseLe_of_cuspRapidDecay_artin_rayClassField hC hA hR, _root_.GlobalTheory.T.baseGe_of_cuspRapidDecay_artin_rayClassField_seriesRat hC hA hR hS,
    _root_.GlobalTheory.T.twist_upper_bound_of_prints hC hA hR tA tC, _root_.GlobalTheory.T.twist_lower_bound_of_prints hC hA hR hS tA tC⟩
end GlobalTheory.BigOn.Exp
end
