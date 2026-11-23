import Formalism.PeriodIntegrals.LocHerm
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalGluing.LocGlueOf
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.LocOProj

theorem local_hermitian_glue : PI.LocHerm.LocGlue :=
  PI.LocHerm.Glue.locGlue_of projectiveOverOrder
