import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CmDataConjIsConjOf
import Mathlib
import Formalism.LocalRingCardinality.DataSpaces
import Formalism.LocalToGlobal.Divisibility.TuplesLemmas
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmData_conj_isConjOf : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : CMData F E), IsConjOf hc.sig := by
  first | exact @GlobalTheory.cmData_sig_isConjOf | exact GlobalTheory.cmData_sig_isConjOf | (intros; apply GlobalTheory.cmData_sig_isConjOf <;> assumption)
