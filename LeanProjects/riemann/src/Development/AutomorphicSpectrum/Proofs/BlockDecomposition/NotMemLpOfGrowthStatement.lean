import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NotMemLpOfGrowth

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.not_mem_Lp_of_growth : ∀ {X : Type} [MeasurableSpace X] (μ : MeasureTheory.Measure X) (f : X → ℝ) (p : ℝ), 0 < p → MeasureTheory.MemLp f (ENNReal.ofReal p) μ → ∀ (E : ℕ → Set X), (∀ j, MeasurableSet (E j)) → Pairwise (Function.onFun Disjoint E) → ∀ (c D B r : ℝ), 0 < c → 0 < B → 0 ≤ r → (∀ j : ℕ, ENNReal.ofReal (c * D ^ j) ≤ μ (E j)) → (∀ j : ℕ, ∀ x ∈ E j, B * r ^ j ≤ |f x|) → D * r ^ p < 1 := by
  first | exact @GlobalTheory.CompanionTheory.Casselman.mul_rpow_lt_one_of_memLp_geometric | exact GlobalTheory.CompanionTheory.Casselman.mul_rpow_lt_one_of_memLp_geometric | (intros; apply GlobalTheory.CompanionTheory.Casselman.mul_rpow_lt_one_of_memLp_geometric <;> assumption)
