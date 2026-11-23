import Formalism.LocalToGlobal.IndefiniteReal.SobolevIteration.ArvOSobPfKer
import Formalism.LocalToGlobal.IndefiniteReal.SobolevIteration.ArvOSobPfChart
import Formalism.LocalToGlobal.IndefiniteReal.SobolevIteration.ArvOSobPfKFin
import Formalism.LocalToGlobal.IndefiniteReal.SobolevIteration.ArvOSobPfAvg

namespace CompanionTheory.D.gk.HC

open Formalism.IndefR.Tow.SobPf

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem sobApprox_holds : SobApprox :=
  sobApprox_of haarExists_holds polyKernel_holds (avgSmooth_of sobChart_holds) avgKFin_holds
    (continuity_of_sobolev_chart sobChart_holds foldCont_holds) (foldBddK_of sobChart_holds)

end CompanionTheory.D.gk.HC
