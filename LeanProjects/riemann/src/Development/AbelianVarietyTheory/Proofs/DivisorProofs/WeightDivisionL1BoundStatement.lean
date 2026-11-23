import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightDivisionL1Bound
import Development.AbelianVarietyTheory.Definitions.Divisors.DividedWeightUnique
import Formalism.MeanHeightDescent.CovolumeFullAssemblyWeighted
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.L2.Indef.Tree NumberField GlobalTheory.MeanTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weight_division_l1_bound : ∀ (ι : Type) [Fintype ι] (N : ℕ) (W : Wts ι N), W.Hyp → W.IsDiv → (W.T : ℝ) * l1 W.u1 ≤ l1 W.u + (Fintype.card ι : ℝ) * N * (W.c0 + 4 * N) ∧ l1 W.u' ≤ l1 W.u1 ∧ ∀ τ i, |W.u' τ i| ≤ |W.u1 τ i| := by
  first | exact @GlobalTheory.MeanTop.divided_weight_size | exact GlobalTheory.MeanTop.divided_weight_size | (intros; apply GlobalTheory.MeanTop.divided_weight_size <;> assumption)
