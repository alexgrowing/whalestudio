import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.NotSquareOfJacobiNegOne
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.MMScale
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.MMModelS
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.MMReadS
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.MMCoord
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.PowerSeriesEmbedding

namespace Formalism.L2.KerInert

variable [Fact _root_.Formalism.L2.Th1.CM.CM2] in
theorem oneCopyTh1S_of_isom (hI : IsomONB) : OneCopyTh1S :=
  oneCopyTh1S_of scale_lattice_bound hI scale_integrality

variable [Fact _root_.Formalism.L2.Th1.CM.CM2] in
theorem oneCopyLoc_of_isom (hI : IsomONB) (hz : AlgZero) : OneCopyLoc :=
  oneCopyLoc_ofS lattice_extension (oneCopyTh1S_of_isom hI) (coordTie_of_algZero hz) MModelS.model_series_algebraic change_of_parameters_const_scale

end Formalism.L2.KerInert
