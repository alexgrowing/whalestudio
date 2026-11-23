import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquaringOpenAtOneAdicCompletionNumberField
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceOpen
open NumberField IsDedekindDomain GlobalTheory.QSA
open scoped Quaternion Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.squaringOpenAtOne_adicCompletion_numberField : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)), SqOpen (v.adicCompletion F) ∧ (𝓝[≠] (0 : v.adicCompletion F)).NeBot := by
  first | exact @GlobalTheory.QSA.sqOpen_and_nhdsNE_zero_neBot_adicCompletion | exact GlobalTheory.QSA.sqOpen_and_nhdsNE_zero_neBot_adicCompletion | (intros; apply GlobalTheory.QSA.sqOpen_and_nhdsNE_zero_neBot_adicCompletion <;> assumption)
