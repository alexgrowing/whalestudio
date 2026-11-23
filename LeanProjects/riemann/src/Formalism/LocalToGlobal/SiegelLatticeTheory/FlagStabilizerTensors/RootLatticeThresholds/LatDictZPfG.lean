import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LatDictZSt
import Formalism.SelfDualUnimodular.LocalLatticeDictionary.SemiGenusLocal
import Formalism.SelfDualUnimodular.LocalLatticeDictionary.AlgebraMapNeZero

namespace Formalism.L2.SG.Pf.LatDictZ

theorem lattice_genus : LatDictZ.LamGenus :=
  Z0.lamGenus_of (Z0.BR.semiGenus_of Z0.SGC.semi_genus_local)

end Formalism.L2.SG.Pf.LatDictZ
