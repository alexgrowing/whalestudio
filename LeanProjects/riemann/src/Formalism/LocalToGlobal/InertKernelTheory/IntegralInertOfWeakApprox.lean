import Formalism.LocalToGlobal.InertKernelTheory.IntegralInertOfWeakApproxTheta
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.AlgKleinPf

namespace Formalism.L2.KerInert

def WeakApproxAndOrthonormalBases : Prop := WAPlaces ∧ OneCopyOrth ∧ IsomONB

variable [Fact _root_.Formalism.L2.Th1.CM.CM2] in
theorem integral_inert_of_weakApprox (h : WeakApproxAndOrthonormalBases) : IntInert :=
  intInert_of combination_fact pairing_fact (weakApprox_of h.1) pullback_torsion pullback_fact AlgP.algebraic_fact_kernels
    power_series_linearity pairs_standard_at_p (basisInv_of_loc unit_substitution_local) tensor_matrix_units_fact
    (thFourInt_of (oneCopyLoc_of_isom h.2.2 AlgP.zero_value_algebraic) (locInv_of unit_substitution_local) four_products_from_one
      (MMOnb.globONB_of h.2.1) AlgP.zero_value_algebraic)

variable [Fact _root_.Formalism.L2.Th1.CM.CM2] in
theorem jets_inert_of_weakApprox (h : WeakApproxAndOrthonormalBases) (hJ : PhiJetInt) : JetsInert :=
  jetsInert_of_int (integral_inert_of_weakApprox h) (orthBasisExists_of (MMOnb.globONB_of h.2.1) (weakApprox_of h.1)) hJ

end Formalism.L2.KerInert
