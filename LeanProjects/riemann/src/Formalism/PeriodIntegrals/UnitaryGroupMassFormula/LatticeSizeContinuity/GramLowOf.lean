import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeSizeContinuity.LatSizeContOfSteps

noncomputable section

open NumberField Matrix
open PI.LatSizeCont

namespace PI.UnitaryGroupMassFormula.LSC.GramLowOf

theorem gramV_eq (I : Formalism.MainNotions.S.AutInst) (x : I.GA) (v : InfinitePlace I.F) {j : ℕ}
    (b : Fin j → Fin I.n → I.E) :
    Size.gramV I x v b =
      ((Formalism.MainNotions.S.uMat (x.1 v)⁻¹ * (I.P v)⁻¹) * Matrix.of (fun i a => I.φ v (b a i)))ᴴ *
        ((Formalism.MainNotions.S.uMat (x.1 v)⁻¹ * (I.P v)⁻¹) * Matrix.of (fun i a => I.φ v (b a i))) := by
  ext a c
  simp only [Size.gramV, Size.coordV, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.mulVec, dotProduct,
    Matrix.of_apply]

end PI.UnitaryGroupMassFormula.LSC.GramLowOf

namespace PI.UnitaryGroupMassFormula.LSC

end PI.UnitaryGroupMassFormula.LSC
