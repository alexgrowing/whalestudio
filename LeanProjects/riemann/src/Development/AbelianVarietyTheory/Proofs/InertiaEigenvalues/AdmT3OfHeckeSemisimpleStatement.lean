import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmT3OfHeckeSemisimple
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.OffRange
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
open GlobalTheory.LiftLeaf GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw Formalism.BasicNotions Formalism.MainNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admT3_of_hecke_semisimple : ∀ (D : D7) (E : IntegralHeckeForms.XD D), IntegralHeckeForms.IsotypicPartsInternalDirectSum D.nexp E → IntegralHeckeForms.GroupAlgebraIntegrality D.nexp → D.nexp.sig_all → HkSS D → IntegralHeckeForms.GoodLatticePoints D.nexp := by
  first | exact @GlobalTheory.EigRed.admT3_of_semisimple_good | exact GlobalTheory.EigRed.admT3_of_semisimple_good | (intros; apply GlobalTheory.EigRed.admT3_of_semisimple_good <;> assumption)
