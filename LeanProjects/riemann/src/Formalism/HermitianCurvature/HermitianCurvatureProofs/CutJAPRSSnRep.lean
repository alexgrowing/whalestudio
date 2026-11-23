import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRFinal
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnRepDone

namespace Formalism.FourierDecayAlt.P.CutMP

theorem modelPlaceBuilt2_of_jf (hJ : JfSmoothDS) : Formalism.FourierDecayAlt.JCT.ModelPlaceBuilt2 :=
  modelPlaceBuilt2_of_polyS hJ JA.SSn.Rep.Core.TC.PR.polynomial_radial_holds

end Formalism.FourierDecayAlt.P.CutMP
