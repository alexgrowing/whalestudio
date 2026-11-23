import Formalism.GradedWeylDivisibility.FockSpaceTableaux.BideterminantMem
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.SumIcoTsubTelescope
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.HighestWeightVectorNeZero
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.HWRowWeight
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.DualWeylSat
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.DualWeylPoint
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.DualWeylRowStable
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.RowDivStable
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.DualWeylRowGraded
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.DualWeylMap
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.DualWeylIntRat
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.WeylLeDual
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.DualWeylNonDom
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.BideterminantDominance
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.DualWeylMul
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.HWRaise
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.WeylRowDivStable
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.RowNuSum
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.FockHerm
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.FockPos
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.FockWeightOrth
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.FockSubAdj
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.FockRowAdj
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.DomPow
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.FockDiagBound
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.DualWeylDominanceOf

namespace Formalism.GradedWeylDivisibility

theorem bidetMem : BideterminantMem := bideterminantMem
theorem hwMem : HWMem := highestWeightVectorMem
theorem hwNe : HWNe := highestWeightVectorNeZero
theorem hwRowWeight : HWRowWeight := highestWeightVectorRowWeight
theorem dualWeylSat : DualWeylSat := dualWeylModuleSaturated
theorem dualWeylPoint : DualWeylPoint := dualWeylModuleMemIff
theorem dualWeylRowStable : DualWeylRowStable := dualWeylModuleRowActionStable
theorem rowDivStable : RowDivStable := dualWeylModuleRowDividedPowerStable
theorem dualWeylRowGraded : DualWeylRowGraded := dualWeylModuleRowGraded
theorem dualWeylMap : DualWeylMap := dualWeylModuleMap
theorem dualWeylIntRat : DualWeylIntRat := dualWeylModuleIntRat
theorem weylLeDual : WeylLeDual := by
  intro R _ r n hn ν hν
  unfold weyl
  rw [Submodule.span_le]
  rintro _ ⟨w, rfl⟩
  induction w with
  | nil => exact hwMem R r n hn ν hν
  | cons x w ih => exact rowDivStable R r n ν x.1 x.2.1 x.2.2 _ ih
theorem dualWeylNonDom : DualWeylNonDom := dualWeylModuleNonDominant
theorem bidetDominance : BideterminantDominance := bideterminantDominance
theorem dualWeylMul : DualWeylMul := dualWeylModuleMul
theorem hwRaise : HWRaise := highestWeightVectorRaising
theorem weylRowDivStable : WeylRowDivStable := weylModuleRowDividedPowerStable
theorem rowNuSum : RowNuSum := rowPartSum
theorem fockHerm : FockHerm := fischerInnerConjSymm_holds
theorem fockPos : FockPos := fischerInnerPos
theorem fockWeightOrth : FockWeightOrth := fischerInnerWeightOrthogonal_holds
theorem fockSubAdj : FockSubAdj := fischerInnerSubstitutionAdjoint
theorem fockRowAdj : FockRowAdj := fischerInnerRowActionAdjoint
theorem domPow : DomPow := dominancePowerProduct_holds
theorem fockDiagBound : FockDiagBound := fockDiagBound_of domPow

end Formalism.GradedWeylDivisibility
