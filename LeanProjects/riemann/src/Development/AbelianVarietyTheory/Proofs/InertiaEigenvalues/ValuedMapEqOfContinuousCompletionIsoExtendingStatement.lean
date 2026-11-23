import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValuedMapEqOfContinuousCompletionIsoExtending
import Mathlib
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valued_map_eq_of_continuous_completionIso_extending : ∀ (E E' : Type) [Field E] [NumberField E] [Field E'] [NumberField E'] [Algebra E E'] (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E)) (w' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E')) (i : w.adicCompletion E ≃+* w'.adicCompletion E'), Continuous i → (∀ x : E, i (algebraMap E _ x) = algebraMap E' _ (algebraMap E E' x)) → ∀ y : w.adicCompletion E, Valued.v (i y) = Valued.v y := by
  first | exact @GlobalTheory.CompletionIsom.valued_v_map | exact GlobalTheory.CompletionIsom.valued_v_map | (intros; apply GlobalTheory.CompletionIsom.valued_v_map <;> assumption)
