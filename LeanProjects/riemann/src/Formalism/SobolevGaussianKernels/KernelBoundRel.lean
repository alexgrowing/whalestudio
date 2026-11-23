import Formalism.SobolevGaussianKernels.GaussianKernelBounds.EichlerEquivalenceHolds
import Mathlib
import Formalism.SobolevGaussianKernels.StatementCS
import Formalism.SobolevGaussianKernels.GaussianKernelBounds.LfProd
import Formalism.SobolevGaussianKernels.GaussianKernelBounds.NeighbourhoodHilbertSchmidtHolds
import Formalism.SobolevGaussianKernels.StatementMV
import Formalism.SobolevGaussianKernels.GaussianKernelBounds.HasDerivAtSphereChartLast
import Formalism.SobolevGaussianKernels.StatementNC

namespace Formalism.SL.Final

theorem eichIsom : Formalism.SL.IwahoriBlocks.EichIsom := Formalism.SL.P.eichler_isometry_holds
theorem eichInv : Formalism.SL.IwahoriBlocks.EichInv := Formalism.SL.P.eichler_inverse_holds
theorem eichMove : Formalism.SL.IwahoriBlocks.EichMove := Formalism.SL.P.eichler_move_holds
theorem eichInt : Formalism.SL.IwahoriBlocks.EichInt := Formalism.SL.P.eichler_integrality_holds
theorem primesOver : Formalism.SL.LF.PrimesOver := Formalism.SL.P.primes_over_holds
theorem frameGram : Formalism.SL.FU.FrameGram := Formalism.SL.P.frame_gram_holds

end Formalism.SL.Final
