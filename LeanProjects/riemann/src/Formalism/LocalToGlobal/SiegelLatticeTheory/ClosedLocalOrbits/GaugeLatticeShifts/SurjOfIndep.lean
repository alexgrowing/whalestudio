import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RightInvOfModular

noncomputable section

open Matrix
open scoped ComplexConjugate

namespace Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.RI

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates

variable {n : ℕ} (ε : Fin n → Bool)

abbrev dl (i : Fin n) : Fin n → ℂ := Pi.single i 1

theorem hJ_dl (i j : Fin n) : hJ ε (dl i) (dl j) = if i = j then (if ε i then 1 else -1) else 0 := by
  unfold hJ
  simp only [dl, Formalism.REAL.Jm, mulVec_diagonal, dotProduct, Pi.star_apply, Pi.single_apply]
  by_cases h : i = j
  · subst h; simp
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases hl : l = i
    · subst hl; simp [h]
    · simp [hl]

end Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.RI
