import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MellinDerivativeLinearComb
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TranslationInv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullFullL
open Matrix MeasureTheory Set Filter Topology
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm GlobalTheory.TorsionForm.OneVec
open scoped Real ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mellin_derivative_linear_comb : ∀ {ι : Type} (s : Finset ι) (c : ι → ℂ) (F : ι → ℝ → ℂ) (T : ι → ℂ), (∀ i ∈ s, IsMellinDeriv (F i) (T i)) → IsMellinDeriv (fun u => ∑ i ∈ s, c i * F i u) (∑ i ∈ s, c i * T i) := by
  first | exact @GlobalTheory.MellinDerivLinear.isMellinDeriv_sum | exact GlobalTheory.MellinDerivLinear.isMellinDeriv_sum | (intros; apply GlobalTheory.MellinDerivLinear.isMellinDeriv_sum <;> assumption)
