import Formalism.LocalToGlobal.PairingIndexBounds.HalvesRecursion.BoundedHalfModels.ModelXiOfParts
import Formalism.LocalToGlobal.PairingIndexBounds.HalvesRecursion.BoundedHalfModels.MovesComposeOfParts
import Formalism.LocalToGlobal.GlobalTheory.GL3.PThIndep
import Formalism.LocalToGlobal.GlobalTheory.GL3.PSelfDual

namespace Formalism.L2.PairingIndexBounds.Rec

theorem model_at_split_places_holds (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.GL3Theta.modelXi D :=
  modelXi_of_parts Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.hermitian_form_integral_values Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.self_dual_lattice D

theorem split_place_moves_compose (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.GL3Theta.movesCompose D :=
  movesCompose_of_parts Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.hermitian_form_integral_values Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.self_dual_lattice D

end Formalism.L2.PairingIndexBounds.Rec
