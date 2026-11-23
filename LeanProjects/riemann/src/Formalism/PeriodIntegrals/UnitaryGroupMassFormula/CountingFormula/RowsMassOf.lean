import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.MassConstUniqueOne
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.AbsNormSpanNatCast

open Formalism.L2.SG.Pf.Cnt

namespace PI.UnitaryGroupMassFormula.CntFormula.RowsMassW

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in
theorem rowsMass_of (hH : HostDict) (hG : RowsGenus) : RowsMass :=
  rowsMass_of_lamGlue hH hG lamGlue

end PI.UnitaryGroupMassFormula.CntFormula.RowsMassW
