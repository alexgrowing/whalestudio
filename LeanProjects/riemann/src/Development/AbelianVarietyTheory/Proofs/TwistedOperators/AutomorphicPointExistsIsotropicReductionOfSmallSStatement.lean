import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AutomorphicPointExistsIsotropicReductionOfSmallS
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
open MeasureTheory NumberField Matrix Formalism.MainNotions.S GlobalTheory.Count Formalism.REAL Formalism.HN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.automorphicPoint_exists_isotropic_reduction_of_small_size : ∀ (I : AutInst) (x : I.GA) (g q : ℕ), 1 ≤ g → 1 ≤ q → 1 ≤ I.n → (∀ v, rkR (I.ε v) ≤ q) → least I x < 1 / 2 → ∃ W, I.IsIsot W ∧ ∀ m ∈ I.NA W, ∃ γ ∈ I.GFset, ∃ k ∈ I.Kg g, ∃ (u : I.Ginf) (A Z : InfinitePlace I.F → Matrix (Fin I.n) (Fin I.n) ℂ), (∀ v, inG (I.ε v) (A v) ∧ inG (I.ε v) (Z v)) ∧ (∀ v, uMat (u v) = NormedSpace.exp (A v) * NormedSpace.exp (Z v)) ∧ m * x = γ * x * (u, k) ∧ Real.sqrt (∑ v, hs (A v)) + Real.sqrt (∑ v, hs (Z v)) ≤ (I.n : ℝ) ^ 2 * Real.sqrt I.f * g * I.rd * (2 * least I x) ^ ((1 : ℝ) / q) / 4 := by
  first | exact @GlobalTheory.DeepPoint.deep_point | exact GlobalTheory.DeepPoint.deep_point | (intros; apply GlobalTheory.DeepPoint.deep_point <;> assumption)
