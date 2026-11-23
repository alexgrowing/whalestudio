import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DividedDifferenceIdealPowerMem
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanOfPowMul
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.divided_difference_ideal_power_mem : ∀ (B : Type) [CommRing B], (∀ n : ℕ, n ≠ 0 → IsUnit (n : B)) → ∀ (d q u : B), IsUnit u → q - 1 = d * u → ∀ (s : ℕ) (x : ℕ → B), (∀ k : ℕ, ∑ i ∈ Finset.range s, (q ^ k - 1) ^ i * Ring.inverse (i.factorial : B) * x i ∈ Ideal.span {d ^ s}) → d * x 1 ∈ Ideal.span {d ^ s} := by
  first | exact @GlobalTheory.FilCoeff.d_mul_x_one_mem_span_pow | exact GlobalTheory.FilCoeff.d_mul_x_one_mem_span_pow | (intros; apply GlobalTheory.FilCoeff.d_mul_x_one_mem_span_pow <;> assumption)
