import Formalism.LocalToGlobal.BesselHermitianTheta.MinfDensity
import Formalism.LocalRingCardinality.DataDIV

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH

namespace Formalism.L2.Theta

def ThetaDivisorCompatibility {D : D7} (X : ThetaX D) (Z : DivX D) : Prop :=
  @ThetaX.TieMY D X Z.QPl Z.finQ Z.qv

end Formalism.L2.Theta

end
