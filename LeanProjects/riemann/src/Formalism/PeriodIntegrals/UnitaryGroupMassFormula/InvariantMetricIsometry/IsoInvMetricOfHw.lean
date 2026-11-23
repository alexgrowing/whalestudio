import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InvariantMetricIsometry.SymmetricMeasureL2NormEqResolutionL2
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InvariantMetricIsometry.HvScalar
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InvariantMetricIsometry.QuotientRank
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InvariantMetricIsometry.HermitianVectorMap

namespace PI.IsoInvMetricW

theorem isoInvMetric_of_hw (hW : HW) : PI.IsoInvMetric.IsoInvMetric :=
  isoInvMetric_of (unit_of metric_mul) (invK_of metric_mul) (stab_of hermitian_vector_map)
    (hvCols_of hermitian_vector_map) norm1' (gen_of quotient_rank hermitian_vector_map) hW

end PI.IsoInvMetricW
