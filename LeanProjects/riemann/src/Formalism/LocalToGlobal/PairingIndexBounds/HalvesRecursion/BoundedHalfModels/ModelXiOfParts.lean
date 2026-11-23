import Formalism.LocalToGlobal.PairingIndexBounds.HalvesRecursion.BoundedHalfModels.Assemble
import Formalism.LocalToGlobal.PairingIndexBounds.HalvesRecursion.BoundedHalfModels.AdicBoxOpenness.ClosureCharacterHolds
import Formalism.LocalToGlobal.PairingIndexBounds.HalvesRecursion.ModelXiAll

namespace Formalism.L2.PairingIndexBounds.Rec

open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

theorem HalvesRec_of (hA : HfIntRec) (hB : SelfDualRec) : HalvesRec :=
  halvesRec_of_clos closure_character_holds low_approximation_holds hA hB

theorem modelXi_of_parts (hA : HfIntRec) (hB : SelfDualRec) (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.GL3Theta.modelXi D :=
  modelXi_all (HalvesRec_of hA hB) D

end Formalism.L2.PairingIndexBounds.Rec
