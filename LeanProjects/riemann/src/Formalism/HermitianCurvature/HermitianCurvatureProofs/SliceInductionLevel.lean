import Formalism.HermitianCurvature.HermitianCurvatureProofs.AsmCastMCastM
import Formalism.HermitianCurvature.HermitianCurvatureProofs.MeasurePreservingSndEmptyBlock
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LowVLift

namespace Formalism.FourierDecayAlt.P

theorem slice_induction_level : Formalism.FourierDecayAlt.KB.SliceStep :=
  Formalism.FourierDecayAlt.P.PBH.sliceStep_of Formalism.FourierDecayAlt.P.PBH.jfStep (Formalism.FourierDecayAlt.P.PBH.asm_pointStepT Formalism.FourierDecayAlt.P.PBH.pointStep)

end Formalism.FourierDecayAlt.P
