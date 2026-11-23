import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutMP2
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutERAsm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutERCapAdjAsm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutERCapAdjS

namespace Formalism.FourierDecayAlt.P.CutMP

theorem energy_reality_holds : EnergyReal :=
  ER.energyReal_of_capAdjInt (ER.capAdjInt_of_scalar ER.capacity_adjoint_scalar)

end Formalism.FourierDecayAlt.P.CutMP
