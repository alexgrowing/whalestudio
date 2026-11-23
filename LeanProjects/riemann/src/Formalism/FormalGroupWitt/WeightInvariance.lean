import Formalism.FormalGroupWitt.FormalGroupWittProofs.AdditiveLawExample
import Formalism.FormalGroupWitt.FormalGroupWittProofs.GroupV
import Formalism.FormalGroupWitt.FormalGroupWittProofs.FunctionalEquationHomVector
import Formalism.FormalGroupWitt.FormalGroupWittProofs.CongrV
import Formalism.FormalGroupWitt.FormalGroupWittProofs.ShiftFE
import Formalism.FormalGroupWitt.FormalGroupWittProofs.ShiftAsm
import Formalism.FormalGroupWitt.FormalGroupWittProofs.HeightV
import Formalism.FormalGroupWitt.FormalGroupWittProofs.WittTeichmullerRoot
import Formalism.FormalGroupWitt.FormalGroupWittProofs.GaussV

namespace Formalism.FG

universe u v w

theorem addLawExample : AddLawExample := additive_law_example
theorem notLawExample : NotLawExample := not_a_law_example
theorem funEqHomV : FunEqHomV.{u, v, w} := functional_equation_hom_vector

end Formalism.FG
