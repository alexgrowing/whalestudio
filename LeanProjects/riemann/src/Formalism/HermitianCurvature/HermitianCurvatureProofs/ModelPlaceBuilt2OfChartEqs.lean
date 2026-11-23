import Formalism.HermitianCurvature.HermitianCurvatureProofs.ModelPlaceBuilt2OfPublished
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEllRegW

namespace Formalism.FourierDecayAlt.P.CutMP

theorem jfSmoothBuilt_of_chartEqs (hE : SmoothTransferRegularity.ChartEqs) : JfSmoothBuilt :=
  SmoothTransferRegularity.jfSmoothBuilt_of_chart hE SmoothTransferRegularity.elliptic_regularity_weighted

theorem modelPlaceBuilt2_of_chartEqs (hE : SmoothTransferRegularity.ChartEqs) : Formalism.FourierDecayAlt.JCT.ModelPlaceBuilt2 :=
  modelPlaceBuilt2_of_jf (jfSmoothBuilt_of_chartEqs hE)

end Formalism.FourierDecayAlt.P.CutMP
