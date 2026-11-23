import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.FinalA
import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.PairedSquareJets.IntDThmBOf
import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.PairedSquareJets.IntDBG

namespace Formalism.L2.Th1.G

theorem intDThmB : IntDThmB := IntDThmB_of intAtD shapeCong
theorem intDThmBGauss : IntDThmBGauss := IntDThmBGauss_of intAtD shapeCong

end Formalism.L2.Th1.G
