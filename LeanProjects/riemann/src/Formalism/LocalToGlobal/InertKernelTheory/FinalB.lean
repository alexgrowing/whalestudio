import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.IntAsm
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.IntEasy
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.IntPull
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.IntStd
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.IntBasis
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.IntTens
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.ThFourIntOf
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.UnitSubstOfLoc
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.MMFour
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.IntUnit
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.DegreeLeOfCoeffProdNe
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.TestVectorMemSchwartzBruhat
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.JetsModel
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.JetsOrth

namespace Formalism.L2.KerInert

def FactsB : Prop :=
  WeakApprox ∧ UnitSubst ∧ UnitSubstLoc ∧ GlobONB ∧ OneCopyLoc ∧ ThMMTransAlgPrime

theorem intInert_ofB (h : FactsB) : IntInert :=
  intInert_of combination_fact pairing_fact h.1 pullback_torsion pullback_fact (AlgGrP.algFact_of_transPrime h.2.2.2.2.2)
    power_series_linearity pairs_standard_at_p (basisInv_of_unitSubst h.2.1) tensor_matrix_units_fact
    (thFourInt_of h.2.2.2.2.1 (locInv_of h.2.2.1) four_products_from_one h.2.2.2.1 (AlgGrP.algZero_of_transPrime h.2.2.2.2.2))

variable [Fact _root_.Formalism.L2.Th1.CM.CM2] in
theorem jetsInert_ofB (h : FactsB) (hJ : PhiJetInt) : JetsInert :=
  jetsInert_of_int (intInert_ofB h) (orthBasisExists_of h.2.2.2.1 h.1) hJ

end Formalism.L2.KerInert
