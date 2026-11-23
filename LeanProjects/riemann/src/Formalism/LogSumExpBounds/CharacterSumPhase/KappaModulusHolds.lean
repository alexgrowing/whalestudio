import Formalism.LogSumExpBounds.StatementC

namespace Formalism.NuclearRankWeightBounds.P

open Matrix Formalism.NuclearRankWeightBounds.C

section
variable {RR : Type*} {K : Type*} [CommRing RR] [CommRing K] [Algebra RR K]

theorem descend_mk {k : ℕ} (Z : Matrix (Fin k) (Fin k) RR) (r : Fin k → K)
    (hZ : LinearMap.range Z.mulVecLin ≤ LinearMap.ker (rowInvMod K Z r)) (v : Fin k → RR) :
    descend K Z r (Submodule.Quotient.mk v) = rowInvMod K Z r v := by
  classical
  unfold descend
  rw [dif_pos hZ]
  rfl

variable {m : ℕ}

end

end Formalism.NuclearRankWeightBounds.P
