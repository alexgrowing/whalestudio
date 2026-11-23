import Formalism.SubspaceCounting.SubspaceCountingProofs.AllButLESmith
import Formalism.SubspaceCounting.SubspaceCountingProofs.ChoiceOfTops
import Formalism.SubspaceCounting.SubspaceCountingProofs.LengthLayers
import Formalism.SubspaceCounting.SubspaceCountingProofs.ManyOrbits
import Formalism.SubspaceCounting.SubspaceCountingProofs.QVandermonde
import Formalism.SubspaceCounting.SubspaceCountingProofs.TopsChoicePartA
import Formalism.SubspaceCounting.SubspaceCountingProofs.TopsChoicePartB
import Formalism.SubspaceCounting.SubspaceCountingProofs.TopsChoicePartC
import Formalism.SubspaceCounting.SubspaceCountingProofs.TopsChoiceCount
import Formalism.SubspaceCounting.SubspaceCountingProofs.SaturatedMember
import Formalism.SubspaceCounting.SubspaceCountingProofs.SubspaceCount
import Formalism.SubspaceCounting.SubspaceCountingProofs.TailConcavity
import Formalism.SubspaceCounting.SubspaceCountingProofs.TailSums
import Formalism.SubspaceCounting.SubspaceCountingProofs.TypeIIDown
import Formalism.SubspaceCounting.SubspaceCountingProofs.TypeIIUp
import Formalism.SubspaceCounting.SubspaceCountingProofs.WalkSharp
import Formalism.SubspaceCounting.SubspaceCountingProofs.ManyOrbitsRefined
import Formalism.SubspaceCounting.SubspaceCountingProofs.ChoiceOfTopsRefined
import Formalism.SubspaceCounting.SubspaceCountingProofs.MarkedRun
import Formalism.SubspaceCounting.SubspaceCountingProofs.DetDivides
import Formalism.SubspaceCounting.SubspaceCountingProofs.DetVal
import Formalism.SubspaceCounting.SubspaceCountingProofs.DetQuotVal
import Formalism.SubspaceCounting.SubspaceCountingProofs.CramerCofactor

namespace Formalism.G0.Top

theorem walkSharp : Formalism.G0.WalkSharp := Formalism.G0.walkSharp_true

theorem manyOrbits : Formalism.G0.ManyOrbits := Formalism.G0.many_orbits

theorem lengthLayers : Formalism.G0.LengthLayers := Formalism.G0.lengthBoundOfLayers

theorem saturatedMember : Formalism.G0.SaturatedMember := Formalism.G0.saturated_member

theorem allButLESmith : Formalism.G0.AllButLESmith := Formalism.G0.all_but_le_smith

theorem choiceOfTops : Formalism.G0.ChoiceOfTops :=
  Formalism.G0.choiceOfTops_of Formalism.G0.tops_choice_part_a Formalism.G0.tops_choice_part_b Formalism.G0.tops_choice_part_c Formalism.G0.tops_choice_count

theorem tailConcavity : Formalism.G0.TailConcavity := Formalism.G0.tail_concavity

theorem tailSums : Formalism.G0.TailSums := Formalism.G0.tail_sums

theorem qVandermonde : Formalism.G0.QVandermonde := Formalism.G0.qVandermondeIdentity

theorem subspaceCount : Formalism.G0.SubspaceCount := Formalism.G0.countSubspacesEq

theorem typeIIUp : Formalism.G0.TypeIIUp := Formalism.G0.type_two_upper

theorem typeIIDown : Formalism.G0.TypeIIDown := Formalism.G0.countAboveRangeCodimFormula

theorem many_orbits_refined : Formalism.G0.ManyOrbitsRefined := Formalism.G0.many_orbits_refined_holds

theorem choice_of_tops_refined : Formalism.G0.TileConditionFailureProbBound := Formalism.G0.choice_of_tops_refined_holds

theorem markedRun : Formalism.G0.MarkedRun := Formalism.G0.marked_run

theorem detDivides : Formalism.G0.DetDivides := Formalism.G0.det_divides

theorem detVal : Formalism.G0.DetVal := Formalism.G0.det_valuation

theorem detQuotVal : Formalism.G0.DetQuotVal := Formalism.G0.det_quotient_valuation

theorem cramerCofactor : Formalism.G0.CramerCofactor := Formalism.G0.cramer_cofactor

end Formalism.G0.Top
