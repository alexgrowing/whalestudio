import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AlgebraicValuesFinite.OrdFEqOfClassOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AlgebraicValuesFinite.FinprodNormEmbedding
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AlgebraicValuesFinite.EvFLocalIdeleSelf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AlgebraicValuesFinite.FactorOne
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AlgebraicValuesFinite.IsIntegralOfMemCompo

noncomputable section

namespace PI.AlgValsFin.W

theorem algValsFin_of_tors (L : Type) [Field L] [NumberField L] (hT : TorsUnits L) : AlgValsFin L :=
  assemble hT (keyIdOf decomp locVal prodNorm) classPow classSame

end PI.AlgValsFin.W
