import Mathlib
import Formalism.PeriodIntegrals.UnipVal
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentValuation.VwIntEqZero

theorem unipVal : PI.UnipVal.UnipVal := fun _ _ _ w =>
  ⟨fun n hn => PI.UnitaryGroupMassFormula.UnipVal.Main.part1 w n hn,
    fun g₁ g₂ a h1 h2 h12 => PI.UnitaryGroupMassFormula.UnipVal.Main.part2 w g₁ g₂ a h1 h2 h12⟩
