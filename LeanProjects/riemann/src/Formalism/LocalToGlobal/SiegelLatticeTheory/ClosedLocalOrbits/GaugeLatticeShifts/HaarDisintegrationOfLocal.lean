import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.HermitianZZEqNeg

namespace Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries

theorem haar_disintegration_of_local (h5 : JacobianCoordinates.P5) (hJ : JacobianCoordinates.JacLoc) (hS : JacobianCoordinates.SecMeasLoc) (hU : JacobianCoordinates.UnimodLoc)
    (hN : JacobianCoordinates.NHLoc) (hR : StepReal) : HaarDisintegrationReal :=
  h5 hJ DiagDCLoc_holds hS hU hN hR

end Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries
