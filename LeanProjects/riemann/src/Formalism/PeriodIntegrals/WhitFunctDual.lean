import Mathlib
import Formalism.PadicSubsetSums.CentralIdempotents.EigenbasisOfDistinctRoots
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GGMirabolicBase

namespace PI

def WhitFunctDual : Prop :=
  Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.GelfandGraevMultOne → Formalism.L2.SG.GGMirabolic.GelfandGraevMultOne

end PI
