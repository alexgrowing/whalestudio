import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.TheoremIIClosedOfTestBound
import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.TransStep
import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.SubstSPtrue

noncomputable section

namespace Formalism.MainNotions.TestSideCounting

open Formalism.MainNotions.Pf14

theorem rest6a (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) : SourcePrimitiveIntegrality D CLa Ck Crk Cdeg :=
  source_integrality_of_substitution transStep substPol 1 one_pos (fun C _ => spStep C) D CLa Ck Crk Cdeg

end Formalism.MainNotions.TestSideCounting
