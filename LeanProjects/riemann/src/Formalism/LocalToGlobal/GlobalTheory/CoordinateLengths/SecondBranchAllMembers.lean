import Formalism.LocalToGlobal.GlobalTheory.CoordinateLengths.SecondBranchOfRationality
import Formalism.LocalToGlobal.GlobalTheory.CoordinateLengths.RatStab

namespace Formalism.L2.GlobalTheoryTheory.LemB

theorem second_branch_all_members : ∀ (D : Formalism.BasicNotions.D7) (u : D.what₂.Word), Formalism.MainNotions.RT.SecondBranchIntegralityUnderForms D u :=
  second_branch_of_rationality ratInC_holds ratGL_holds

end Formalism.L2.GlobalTheoryTheory.LemB
