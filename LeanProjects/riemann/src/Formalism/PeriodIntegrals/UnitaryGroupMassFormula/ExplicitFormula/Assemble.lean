import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.ExplicitFormulaFromGluing
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.GoodHeight
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.PerronKernelB
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.PerronSumBound
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.PerronTruncOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.PerronLOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.RectProofs
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.LStructC
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.Contour
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.LogDerivBounds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.RegZero
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.ShiftBoundOf

noncomputable section

namespace PI.EF

theorem explicitFormula_of_local (hZW : PI.ZerosWindow) (hLL : ∃ C, 0 < C ∧ LocalLemma C)
    (hSides : GlueSides) : PI.ExplicitFormula := by
  obtain ⟨Cw, hCw, hW⟩ := hZW
  obtain ⟨Cl, hCl, hL⟩ := hLL
  have hκ0 : (0 : ℝ) < 12 * Cw + 4 := by linarith
  have hCI : ContourIdentity := glueContour rectResidue zeroLocus zerosFinite
  have hH : ∃ C, 0 < C ∧ LogDerivHoriz (12 * Cw + 4) C :=
    ⟨_, by have := mul_pos hCw hκ0; linarith, logDerivHoriz_of hCw.le hCl.le hκ0 hW hL zeroLocus⟩
  have hLf : ∃ C, 0 < C ∧ LogDerivLeft C := ⟨_, by linarith, logDerivLeft_of hCw.le hCl.le hW hL zeroLocus⟩
  obtain ⟨Cs, hCs, hS⟩ := hSides (12 * Cw + 4) hκ0 hH hLf
  exact explicitFormula_of_perron_shift (12 * Cw + 4)
    ⟨500, by norm_num, PK.perronL_of (by norm_num) (PK.perronTrunc_of PK.perron_kernel_single_term perronSumBound)⟩
    ⟨Cs + (Cw + Cl) + 3, by linarith,
      shiftBound_of hκ0 hCs.le (by linarith) regularPart hCI hS (regAtZero_of hW hL)⟩
    (goodHeightExists_of hCw.le hW)
    ⟨4 * Cw, by linarith, truncChange_of hCw.le hW⟩ zerosFinite

end PI.EF
