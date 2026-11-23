import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.LevelSAllOfSemiNHSHeisLev
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.SemiTop
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.ModulusAllExtensions
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.NCAsmM

namespace PI.LevelKSplit.W.Top6

theorem levelSplitting_of_heisenberg_levi (hH : PI.LevelKSplit.W.NC.HeisPAll) (hL : PI.LevelKSplit.W.NC.LevPAll) :
    PI.LevelKSplit.LevelSAll :=
  PI.LevelKSplit.W.NC.levelSAll_of_semiNHS_heis_lev PI.LevelKSplit.W.SemiT.semidirect_topological_all hH hL
    PI.LevelKSplit.W.MVA.modulus_all_extensions PI.LevelKSplit.W.NCA.normal_conjugation_all

end PI.LevelKSplit.W.Top6
