import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.SiegelMassRatios.IdCell
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitNormRoot.UnitNormRootMain

theorem unitNormRoot (E : Type) [Field E] [NumberField E] [StarRing E] : Formalism.L2.SG.IdCell.NormRoot E :=
  PI.UnitNormRootW.unitNormRoot_main
