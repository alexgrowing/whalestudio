import Formalism.LocalToGlobal.InertKernelTheory.AdmissibleEleventhInert
import Formalism.LocalToGlobal.InertKernelTheory.FinalB
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.GenusOneWittExistsOf
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.GlobalOrthonormalBasisFour
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.IntWeak
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.OneCopyTh1SOfIsom

namespace Formalism.L2.KerInert

variable [Fact _root_.Formalism.L2.Th1.CM.CM2] in
theorem genus_one_witt_exists : GenusOneWittExists := ModelP.genus_one_witt_exists_of (GenusOneDatumExistence.genus_one_datum_exists Sigma.invAlg')

variable [Fact _root_.Formalism.L2.Th1.CM.CM2] in
theorem unit_substitution_local : UnitSubstLoc :=
  unitSubstLoc_of_model (ModelP.endIntInertAll_of endomorphisms_integral_inert genus_one_witt_exists)
    (ModelP.phNormOKInertAll_of phi_norm_inert_prime endomorphisms_integral_inert genus_one_witt_exists)
    (ModelP.biaddInertAll_of (Dict.biaddInert_of (Sigma.sigmaCurveInert_of Sigma.invAlg' Sigma.secondEisensteinAlgebraic))
      genus_one_witt_exists)

def WeakApproxOrthonormalBasesThetaAlgebraicity : Prop := WAPlaces ∧ OneCopyOrth ∧ IsomONB ∧ ThMMTransAlgPrime

variable [Fact _root_.Formalism.L2.Th1.CM.CM2] in
theorem factsB_of (h : WeakApproxOrthonormalBasesThetaAlgebraicity) : FactsB :=
  ⟨weakApprox_of h.1, unitSubst_of_loc unit_substitution_local, unit_substitution_local, MMOnb.globONB_of h.2.1,
    oneCopyLoc_of_isom h.2.2.1 (AlgGrP.algZero_of_transPrime h.2.2.2), h.2.2.2⟩

variable [Fact _root_.Formalism.L2.Th1.CM.CM2] in
theorem integral_inert_of_weakApprox_theta (h : WeakApproxOrthonormalBasesThetaAlgebraicity) : IntInert := intInert_ofB (factsB_of h)

variable [Fact _root_.Formalism.L2.Th1.CM.CM2] in
theorem jets_inert_of_weakApprox_theta (h : WeakApproxOrthonormalBasesThetaAlgebraicity) (hJ : PhiJetInt) : JetsInert := jetsInert_ofB (factsB_of h) hJ

end Formalism.L2.KerInert
