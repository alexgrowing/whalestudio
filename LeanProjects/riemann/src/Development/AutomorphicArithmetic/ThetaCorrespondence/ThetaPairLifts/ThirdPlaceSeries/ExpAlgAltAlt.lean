import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExponentialAlgebraicityFromReciprocity
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExpAlgAlt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExpAlgOfSerAlg
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PointCasesStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ScaleRootOfPrintStatement

set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
namespace GlobalTheory.BigOn.Exp
theorem expAlg_alt : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt →
    GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.SeriesRat → _root_.GlobalTheory.BigOn.Exp.ExpAlgAlt := fun h1 h2 h3 h4 =>
  _root_.GlobalTheory.BigOn.Exp.expAlg_of_serAlg_alt (_root_.GlobalTheory.BigOn.Exp.serAlg_of_serRef_scaleRoot (_root_.GlobalTheory.T.series_ref_of_decay_artin_ray_seriesRat h1 h2 h3 h4) (_root_.GlobalTheory.T.scale_root_of_reciprocity_inputs h1 h2 h3 h4))
end GlobalTheory.BigOn.Exp
end
end
