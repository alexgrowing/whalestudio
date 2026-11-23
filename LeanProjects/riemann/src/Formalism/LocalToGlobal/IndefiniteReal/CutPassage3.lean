import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.CutPassage3SOfSteps
import Formalism.LocalToGlobal.IndefiniteReal.RhoSpec
import Formalism.LocalToGlobal.IndefiniteReal.MajorantAtBaseEqInnerOfPackage
import Formalism.LocalToGlobal.IndefiniteReal.RowGSurj
import Formalism.LocalToGlobal.IndefiniteReal.PGoodOfRho

namespace Formalism.IndefR.CxPass

theorem steps3 : Steps3 := fun _ _ _ _ _ _ _ _ _ _ _ _ I =>
  ⟨I.pRho, I.pJ, I.pRange, I.pMet_of I.pJt I.pJ, I.pFrames, I.pUni_of I.pJt I.pRho, I.pLat_of I.pJt,
    I.pGLat_of I.pJt I.pRho, I.pSand_of I.pJt I.pJ I.pRho I.pRange, fun _ _ _ _ _ _ τ => I.pGood_of I.pJt I.pRho τ⟩

theorem cutPassage3S : CutPassage3S := cutPassage3S_of_steps steps3

theorem cutPassage3 : CutPassage3 := cutPassage3_of_S cutPassage3S

end Formalism.IndefR.CxPass
