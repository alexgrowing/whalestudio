import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.HWLine
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.HWLineTall
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.FockQPos
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.FockQBilin
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.FockQRowDivAdj
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.RowDivClosedGraded
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.HWInClosed
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.NablaTallZero
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.ClosedEqNabla
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.WeylEqNablaQ
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.WeylRationalOf

namespace Formalism.GradedWeylDivisibility

theorem hwLine : HWLine := highest_weight_line
theorem hwLineTall : HWLineTall := highest_weight_line_tall
theorem fockQPos : FockQPos := fischerInnerRatPos
theorem fockQBilin : FockQBilin := fischerInnerRatBilinear
theorem fockQRowDivAdj : FockQRowDivAdj := fock_space_row_divided_adjoint
theorem rowDivClosedGraded : RowDivClosedGraded := row_divided_closed_graded
theorem hwInClosed : HWInClosed := hwInClosed_of hwLine rowDivClosedGraded
theorem closedEqNabla : ClosedEqNabla := closedEqNabla_of hwInClosed fockQPos fockQBilin fockQRowDivAdj
theorem weylEqNablaQ : WeylEqNablaQ := weylEqNablaQ_of closedEqNabla

theorem weylRational : WeylRational := weyl_module_rational weylEqNablaQ

end Formalism.GradedWeylDivisibility
