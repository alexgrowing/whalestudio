import Mathlib
import Formalism.PeriodIntegrals.DiscIn
import Formalism.PeriodIntegrals.ZerosWindowIn
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.Assemble
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.PerronGlue
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.LocalProofs
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.LogWindowLe
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.LGrowthFinal

noncomputable section

namespace PI.EF

theorem localLemma_of_helpers (hZW : PI.ZerosWindow) (hDF : PI.DiscFactor) (hDL : PI.DiscLog)
    (hLB : PI.LBoundRight) (hZB : PI.ZetaBoundRight) (hLI : PI.LInvRight) :
    ∃ C, 0 < C ∧ LocalLemma C :=
  localLemma_of hLI (localAbstract_of hDF hDL)
    ⟨7, max 300000 53946, by norm_num, lt_max_of_lt_left (by norm_num),
      lGrowth_of hLB (zetaGrowth_of hZB)⟩ zeroLocus hZW

theorem explicitFormula_main (hZW : PI.ZerosWindow) (hDF : PI.DiscFactor) (hDL : PI.DiscLog)
    (hLB : PI.LBoundRight) (hZB : PI.ZetaBoundRight) (hLI : PI.LInvRight) : PI.ExplicitFormula :=
  explicitFormula_of_local hZW (localLemma_of_helpers hZW hDF hDL hLB hZB hLI) perron_gluing_sides

end PI.EF
