import Mathlib
import Formalism.PeriodIntegrals.DivisionRowsRationalLattice
import Formalism.PeriodIntegrals.IdxCalc
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PowerSpans.SpanPowSmul
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.DvIdxCalc

theorem dvProjC_of (h : PI.Dv.IdxCalc) : PI.Dv.ProjC := PI.Dv.ProjCW.projC_of h

theorem projection_kernel_index : PI.Dv.ProjC := dvProjC_of division_index_calc
