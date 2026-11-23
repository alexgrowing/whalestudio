import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTRRotCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTRMove
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTRConst
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCCurvFinal
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTRTopAct
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTRInt
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTRTrans
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTConnReal
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCRefCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCCurvTr
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCRefAn
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCHolRest
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCLocal
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTConnAnn
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTConnFinal
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGenTransferCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGenTransferFn
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTKLine
import Formalism.HermitianCurvature.HermitianCurvatureProofs.cut_GCore_GTSS
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCFinal
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddDone

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

theorem gTCRefTrace_of_rotK (h : GTRRotK) : GTCRefTrace :=
  gTCRefTrace_of_cutK radial_gauge_move radial_gauge_constant_holds top_normal_form_of_curvature top_action_on_gauge_holds h radial_gauge_integrality_holds radial_gauge_transition_holds gauge_reality_holds

theorem gTCRef_of_rotK (h : GTRRotK) : GTCRef :=
  gTCRef_of_cut gauge_reality_holds curvature_identity_holds curvature_trace_holds (gTCRefTrace_of_rotK h) reference_annulus_holds

theorem gTConn_of_rotK (h : GTRRotK) : GTConn :=
  gTConn_of_leaves gauge_locality_holds gauge_reality_holds (gTCCurv_of_ref (gTCRef_of_rotK h)) (gTCHol_of_ref (gTCRef_of_rotK h)) annulus_condition_holds

theorem genTransfer_of_rotK (h : GTRRotK) : GenTransfer :=
  genTransfer_of_cut GT.gauge_function_holds gauge_kappa_holds (gTConn_of_rotK h) second_shift_gauge_holds

theorem gCore_of_rotK (h : GTRRotK) : GCore := gCore_of_genTransfer (genTransfer_of_rotK h)

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

namespace Formalism.FourierDecayAlt.P.CutMP

theorem modelPlaceBuilt2_of_rotK (hJ : JfSmoothDS) (hR : Gauge.GC.GTRRotK) (h : JA.SSn.SSnRep) :
    Formalism.FourierDecayAlt.JCT.ModelPlaceBuilt2 :=
  modelPlaceBuilt2_of_ssnRep hJ (Gauge.GC.genTransfer_of_rotK hR) h

end Formalism.FourierDecayAlt.P.CutMP
