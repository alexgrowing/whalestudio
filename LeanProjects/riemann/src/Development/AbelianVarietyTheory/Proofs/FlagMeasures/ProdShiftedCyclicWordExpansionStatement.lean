import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ProdShiftedCyclicWordExpansion
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsIsHaarMeasureSUJ
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.DSSU
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prod_shifted_cyclic_word_expansion : ∀ (R : Type) [Ring R] [Algebra ℂ R] (n : ℕ) (T : Fin n → Fin n → R) (c : ℂ) (k : ℕ), ∑ a : Fin (k + 1) → Fin n, ((cycWord a).map (fun p => T p.1 p.2 + if p.1 = p.2 then algebraMap ℂ R c else 0)).prod = algebraMap ℂ R (c ^ (k + 1) * n) + ∑ j ∈ range (k + 1), algebraMap ℂ R (((k + 1).choose (j + 1) : ℂ) * c ^ (k - j)) * ∑ a : Fin (j + 1) → Fin n, ((cycWord a).map (fun p => T p.1 p.2)).prod := by
  first | exact @GlobalTheory.TraceBinom.trace_binomial | exact GlobalTheory.TraceBinom.trace_binomial | (intros; apply GlobalTheory.TraceBinom.trace_binomial <;> assumption)
