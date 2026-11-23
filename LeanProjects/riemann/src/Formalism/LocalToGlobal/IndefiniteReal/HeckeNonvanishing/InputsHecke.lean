import Formalism.UnipotentAdelicQuotients.ThmBInHecke
import Formalism.LocalToGlobal.IndefiniteReal.RealSeparation.NotRootUnity
import Formalism.LocalToGlobal.IndefiniteReal.HeckeNonvanishing.Imports

noncomputable section

open Formalism.BasicNotions Formalism.L2.Theta

namespace Formalism.IndefR.ThmB.InputsHecke

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem isCMExt (D : D7) : HeckeCharacterZeroLocus.ThmBIn.IsCMExt D.host.F D.host.E D.sp.cm.sig :=
  ⟨D.sp.cm.totReal, D.sp.cm.cmUnram.1, D.sp.cm.deg2, fun τ x => D.sp.cm.cmUnram.2.1 τ x⟩

end Formalism.IndefR.ThmB.InputsHecke

end
