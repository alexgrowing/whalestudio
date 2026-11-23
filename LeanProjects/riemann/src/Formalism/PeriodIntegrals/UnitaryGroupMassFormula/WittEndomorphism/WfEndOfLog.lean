import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WittEndomorphism.FlogConstantCoeff
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WfRing
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WfSubst

namespace PI.WfEndProof

theorem wfEnd_of_log (hL : WfLog) : WfEnd := wfEnd_of witt_ring_structure witt_substitution hL

end PI.WfEndProof
