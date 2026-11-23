import Formalism.SharpRestriction.LevelLetterCocycles.BaseChangeOfCoefficientJump
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.BaseCoefJumpProof

namespace Formalism.MainNotions.UnusedSlot80

open Formalism.BasicNotions

theorem base_change_statement (D : D7) : H1fBaseChangeTheorem D := BCF.base_change_statement_of_jump Formalism.MainNotions.N.GlobalTheory.coefficient_jump_general D

theorem base_change_every_theory (Th : LocTheory) : Formalism.MainNotions.WachCoordinates.admBC Th := BCF.base_change_of_coefficient_jump Formalism.MainNotions.N.GlobalTheory.coefficient_jump_general Th

end Formalism.MainNotions.UnusedSlot80
