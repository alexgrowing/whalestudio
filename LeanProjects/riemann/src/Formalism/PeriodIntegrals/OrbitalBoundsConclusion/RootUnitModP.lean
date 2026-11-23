import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.SiegelMassRatios.IdCell
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RootsOfUnityModPrime.RootUnitModPMain

theorem rootUnitModP (E : Type) [Field E] [NumberField E] : Formalism.L2.SG.IdCell.RootModP E :=
  PI.RootUnitModP.W.rootOfUnity_eq_one_mod_prime E

theorem root_of_unity_mod_p (E : Type) [Field E] [NumberField E] : Formalism.L2.SG.IdCell.RootModP E :=
  rootUnitModP E
