import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDGaugeQQAsm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEnergyTr
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEnergyReal
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCFinal

namespace Formalism.FourierDecayAlt.P.CutMP

theorem modelPlaceBuilt2_of_genTransfer (hJ : JfSmoothDS) (hG : Gauge.GC.GenTransfer)
    (hD : JDecayTrQQ) (hA : JAdjTrQQ) : Formalism.FourierDecayAlt.JCT.ModelPlaceBuilt2 :=
  modelPlaceBuilt2_of_openQQ hJ (Gauge.GC.gCore_of_genTransfer hG) energy_trace_identity_holds energy_reality_holds hD hA

end Formalism.FourierDecayAlt.P.CutMP
