import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.HaarGramPositivity.ContDiffConjTranspose
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.HaarGramPositivity.EpowMulOfKill
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.HaarGramPositivity.GramStrictPos
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.HaarGramPositivity.AdjointInv

namespace PositivityTheory.RgBcC

theorem fr0Laws_of (hR : RmLaws) (hG : GamMul) (hM : MtLaws) (hD : GamDer) : MatrixFrechetDerivativeAtZeroLaws := Cxe.fr0Laws_of hR hG hM hD

theorem swapLaws_of (hR : RmLaws) : SwapLaws := Cxe.swapLaws_of hR

example : EigProd := eigProd
example : MatrixFrechetDerivativeAtZeroLaws → Avg := avg_of
example : MatrixFrechetDerivativeAtZeroLaws → Avg → FrOne := frOne'
example : MatrixFrechetDerivativeAtZeroLaws → Avg → FrMulK := frMulK'
example : MatrixFrechetDerivativeAtZeroLaws → Avg → FrIso := frIso'
example : MatrixFrechetDerivativeAtZeroLaws → Avg → FrCont := frCont'

end PositivityTheory.RgBcC
