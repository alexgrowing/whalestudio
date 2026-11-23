import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutTop
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDQQAsm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.JAdjTrQQOfThree
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAStarOp

namespace Formalism.FourierDecayAlt.P.CutMP

theorem modelPlaceBuilt2_of_hat (hJ : JfSmoothDS) (hG : Gauge.GC.GenTransfer)
    (hHat : JDHatOpQQ) (hBdd : JA.JABddOpQQ) : Formalism.FourierDecayAlt.JCT.ModelPlaceBuilt2 :=
  modelPlaceBuilt2_of_genTransfer hJ hG (jDecayTrQQ_of_open hHat) (JA.jAdjTrQQ_of_three hHat hBdd JA.star_operator_transfer_holds)

end Formalism.FourierDecayAlt.P.CutMP
