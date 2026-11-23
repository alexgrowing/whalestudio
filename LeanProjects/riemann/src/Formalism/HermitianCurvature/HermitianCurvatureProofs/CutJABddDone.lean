import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddKapShared
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddSSnFinal
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddSSnChainPf
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnGeom
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnRepDatumUnit
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAGaugeLines
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRhoExists
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddScalProof
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddOp
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ModelPlaceBuilt2OfBdd

namespace Formalism.FourierDecayAlt.P.CutMP.JA

theorem kappa_quadratic_bound_holds : JABddKapQQ :=
  jABddKapQQ_of_shared second_shift_geometry_holds rho_projection_existence gauge_lines_holds SSn.Rep.datum_unit_norm_holds

theorem jABddOpQQ_of_ssnRep (h : SSn.SSnRep) : JABddOpQQ :=
  jABddOpQQ_of_bddLeaves bounded_scalar_transfer_holds kappa_quadratic_bound_holds
    (SSn.jABddSSnQQ_of_leaves SSn.ChainPf.chain_bound_holds second_shift_geometry_holds h)
    (SSn.jABddSSnStarQQ_of_leaves SSn.ChainPf.chain_bound_holds second_shift_geometry_holds h)

end Formalism.FourierDecayAlt.P.CutMP.JA

namespace Formalism.FourierDecayAlt.P.CutMP

theorem modelPlaceBuilt2_of_ssnRep (hJ : JfSmoothDS) (hG : Gauge.GC.GenTransfer) (h : JA.SSn.SSnRep) :
    Formalism.FourierDecayAlt.JCT.ModelPlaceBuilt2 :=
  modelPlaceBuilt2_of_bdd hJ hG (JA.jABddOpQQ_of_ssnRep h)

end Formalism.FourierDecayAlt.P.CutMP
