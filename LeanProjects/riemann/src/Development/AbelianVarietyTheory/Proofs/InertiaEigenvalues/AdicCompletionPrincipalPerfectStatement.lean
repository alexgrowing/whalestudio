import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdicCompletionPrincipalPerfect
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adicCompletion_principal_perfect : ∀ (l : ℕ) [Fact l.Prime] (V : Type) [CommRing V] [CharP V l] [PerfectRing V l] (x : V), ((l : ℕ) : AdicCompletion (Ideal.span {x}) V) = 0 ∧ Function.Bijective fun y : AdicCompletion (Ideal.span {x}) V => y ^ l := by
  first | exact @GlobalTheory.PerfectCompletion.perfect | exact GlobalTheory.PerfectCompletion.perfect | (intros; apply GlobalTheory.PerfectCompletion.perfect <;> assumption)
