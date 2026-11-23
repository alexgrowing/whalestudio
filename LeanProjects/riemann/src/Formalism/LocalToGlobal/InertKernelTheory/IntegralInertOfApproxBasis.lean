import Formalism.LocalToGlobal.InertKernelTheory.IntegralInertOfWeakApprox
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.GlobalOrthonormalBasisFour
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.MMIsom
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.MMConj
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.BlockFourfoldHOneEqHOne
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.ConjugationFixedClosure

namespace Formalism.L2.KerInert

theorem isomONB_ofLB (hLB : LocBasisMM) : IsomONB :=
  isomONB_of_facts conjugation_extension_inert hLB rational_coordinates conjugation_fixed_closure

variable [Fact _root_.Formalism.L2.Th1.CM.CM2] in

theorem integral_inert_of_approx_basis (hWA : WAPlaces) (hLB : LocBasisMM) : IntInert :=
  integral_inert_of_weakApprox ⟨hWA, one_theta_orthonormal, isomONB_ofLB hLB⟩

end Formalism.L2.KerInert
