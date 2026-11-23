import Mathlib
import Formalism.PeriodIntegrals.SqPair
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalCartanPairs.FiniteAdeleIdempotentOfFMulSelf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalCartanPairs.HyperbolicPlane
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalCartanPairs.PairDichotomy
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalCartanPairs.PairSelection
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalCartanPairs.CmpSplit
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalCartanPairs.StepGlue

theorem local_cartan_pair : PI.SqPair.LocCartanPair :=
  PI.SqPair.LCP.locCartanPair_of PI.SqPair.LCP.pair_dichotomy PI.SqPair.LCP.base_lagrangian
    (PI.SqPair.LCP.step_of PI.SqPair.LCP.pair_selection PI.SqPair.LCP.hyperbolic_plane
      PI.SqPair.LCP.pair_split')
