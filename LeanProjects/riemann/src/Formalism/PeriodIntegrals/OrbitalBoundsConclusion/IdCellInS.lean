import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdentityCellTrace.TermIdIffInSOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdentityCellTrace.TraceOneHolds

theorem term_id_iff_in_s (D : Formalism.BasicNotions.D7) (u u' : D.what₂.Word) : Formalism.L2.SG.FourParts.TermIdIffInS D u u' :=
  PI.UnitaryGroupMassFormula.IdCellInSW.termIdIffInS_of D (PI.UnitaryGroupMassFormula.IdCellInSW.traceOne_holds D) u u'
